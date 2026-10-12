import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.BoseRowQ2.gchiAtMaskOfMatLe
import Submission.Work.BoseRowQ2.latticeComm_le

/-!
# `Submission/Work/BoseRowQ2/rowGchiN_aux` — the commutator route to `RowGchiN`

This module proves the one-body matrix row

`⟨u, GchiA u⟩ ≤ (1+ε)⟨u, GchiF u⟩ + (1+1/ε)(C₁/κ_lat)²‖u‖²`

(`oneBodyRow`, FS l.3253 at the *free* number `T.N`), which is the input of the Fock-level row
`Work.BoseRowQ2.rowGchiN_honest`.

The argument is the one recorded in `LEAD_RULING_NH.md` §2 (the "commutator route"):

* `⟨u, GchiA u⟩ = Σ_k (bfun k)² + ⟨w, Tail w⟩` (the lattice-Parseval split, `GchiA_split`);
* `bfun k = φ k · v k + r k` where `v k` is the χ-transform of the θ-coordinate vector and `r`
  is the *commutator* `[χ, f_L(D)]`, bounded by the Lipschitz property of the low cut-off
  (`comm_bound`);
* `v k = ⟨f_k,u⟩ − ⟨h_k,z⟩` with the deviation `h_k = f_k − Σ_i χ̂(K_k−K_i)g_i`, whose low-band
  norm is controlled by the χ̂-cube-complement tail (`dev_bound`).

The constants are collected in `rowC` (the row's `C₁`) and the cube size in `Ng0`; the row is
uniform in the dilation parameter because `κ_lat = d⁻² ≥ 1` whenever `μa³ ≤ 1`
(`one_le_honCutRad`).
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory

namespace Work.BoseRowQ2

open Work.BoseB4 Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix
open Work.UBB Work.BoseRowsFS
open Work.BoseBox RowGchiMaskRowAux

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace RowGchiNAux

variable {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}

/-! ## 1. The constants of the row -/

/-- The Lipschitz constant of the `LowCut` profile (`lowCut_lipschitz`). -/
noncomputable def lipC (fc : Work.BoseBoxFix.LowCut) : ℝ :=
  Classical.choose (lowCut_lipschitz fc)

theorem lipC_nonneg (fc : Work.BoseBoxFix.LowCut) : 0 ≤ lipC fc :=
  (Classical.choose_spec (lowCut_lipschitz fc)).1

theorem abs_sub_le_lipC (fc : Work.BoseBoxFix.LowCut) (x y : ℝ) :
    |fc.f x - fc.f y| ≤ lipC fc * |x - y| :=
  (Classical.choose_spec (lowCut_lipschitz fc)).2 x y

/-- `S₁ ≥ 0`. -/
theorem chiS1_nonneg : 0 ≤ chiS1 := by
  rw [chiS1_eq_tsum_chiHatWeight]
  exact tsum_nonneg fun m => chiHatWeight_nonneg m

/-- The constant of the `Tail`-entry bound (`tailEntry_le`). -/
noncomputable def tailE : ℝ := Classical.choose tailEntry_le

theorem tailE_nonneg : 0 ≤ tailE := (Classical.choose_spec tailEntry_le).1

theorem tailE_spec (N : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hR : 1 ≤ 2 * Real.pi * ((N : ℝ) + 1) - L) (a c : Fin 3 → ℤ)
    (ha : ‖Work.BoseB4.vec a‖ ≤ L) (hc : ‖Work.BoseB4.vec c‖ ≤ L) :
    |∑' m : {m : Fin 3 → ℤ // m ∉ cube N},
        chiHat (Work.BoseB4.vec (m.val - a)) * chiHat (Work.BoseB4.vec (m.val - c))|
      ≤ tailE / (2 * Real.pi * ((N : ℝ) + 1) - L) ^ 101 :=
  (Classical.choose_spec tailEntry_le).2 N L hL hR a c ha hc

/-- The constant of the `Tail`-quadratic-form bound (`tail_quad_le`). -/
noncomputable def tailQ : ℝ := Classical.choose tail_quad_le

theorem tailQ_nonneg : 0 ≤ tailQ := (Classical.choose_spec tail_quad_le).1

theorem tailQ_spec (N : ℕ) (L : ℝ) (hL : 0 ≤ L) (hR : 1 ≤ rad N L) (b : Lab N → ℝ)
    (hb : ∀ i, b i ≠ 0 → ‖Work.BoseB4.vec (labVec N i)‖ ≤ L) :
    (∑ i : Lab N, ∑ j : Lab N, b i * b j * Tail N i j)
      ≤ tailQ * (Fintype.card (Lab N) : ℝ) / rad N L ^ 101 * ∑ i : Lab N, (b i) ^ 2 :=
  (Classical.choose_spec tail_quad_le).2 N L hL hR b hb

/-- **The row constant `C₁`** of FS l.3253 at the free number `T.N`: the commutator constant
`C_fc·S₁` plus the deviation and `Tail` payloads, with room. -/
noncomputable def rowC (fc : Work.BoseBoxFix.LowCut) : ℝ :=
  4 * (lipC fc * chiS1 + (27 * tailE + 1) + (27 * tailQ / Real.pi ^ 101 + 1) + 1)

theorem tailE_sum : rowC fc
    = 4 * (lipC fc * chiS1 + (27 * tailE + 1) + (27 * tailQ / Real.pi ^ 101 + 1) + 1) := rfl

theorem rowC_nonneg (fc : Work.BoseBoxFix.LowCut) : 0 ≤ rowC fc := by
  rw [rowC]
  have h1 : 0 ≤ lipC fc * chiS1 := mul_nonneg (lipC_nonneg fc) chiS1_nonneg
  have h2 : 0 ≤ 27 * tailE + 1 := by have := tailE_nonneg; linarith
  have h3 : 0 ≤ 27 * tailQ / Real.pi ^ 101 + 1 := by
    have := tailQ_nonneg
    positivity
  linarith

/-- `√x ≤ x + 1` for `x ≥ 0`. -/
lemma sqrt_le_add_one {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ≤ x + 1 := by
  have h1 : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
  nlinarith [Real.sqrt_nonneg x, h1, sq_nonneg x]

/-- **The cube size of the row**: just large enough that the no-wrap and lattice-gap conditions
hold (`2κ_lat/π + 1`). -/
noncomputable def Ng0 (v : E3 → ℝ) (μ : ℝ) : ℕ := ⌈2 * honCutRad v μ / Real.pi + 1⌉₊

theorem le_Ng0 (v : E3 → ℝ) (μ : ℝ) :
    2 * honCutRad v μ / Real.pi ≤ (Ng0 v μ : ℝ) := by
  have h := Nat.le_ceil (2 * honCutRad v μ / Real.pi + 1)
  rw [Ng0]
  linarith

theorem two_mul_honCutRad_le (v : E3 → ℝ) (μ : ℝ) {N : ℕ} (hN : Ng0 v μ ≤ N) :
    2 * honCutRad v μ ≤ Real.pi * (N : ℝ) := by
  have h := le_Ng0 v μ
  have h2 : (Ng0 v μ : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hN
  rw [div_le_iff₀ Real.pi_pos] at h
  have h3 : (Ng0 v μ : ℝ) * Real.pi ≤ (N : ℝ) * Real.pi :=
    mul_le_mul_of_nonneg_right h2 (le_of_lt Real.pi_pos)
  nlinarith [h, h3]

/-! ## 2. `κ_lat ≥ 1` in the dilute régime -/

theorem honCutRad_eq_d (v : E3 → ℝ) (μ : ℝ) (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v) :
    honCutRad v μ = (paramsAt μ (_root_.BoseGases.a v)).d ^ (-(2 : ℝ)) := by
  set a := _root_.BoseGases.a v with ha
  have ht : 0 < μ * a ^ 3 := by positivity
  have hKl : 0 < (paramsAt μ a).Kl := fsXp_pos (c := -(3 / 2)) ht
  have hd : 0 < (paramsAt μ a).d := fsXp_pos (c := 6) ht
  have hside : 0 < sideAt μ a := boxSide_pos hμ hav hKl
  have hμa : 0 < μ * a := mul_pos hμ hav
  rw [honCutRad, honKap, ellH, if_pos hside, sideAt, boxSide]
  have h1 : ((paramsAt μ a).Kl * (paramsAt μ a).d ^ 2) ^ (-(1 : ℝ))
      = ((paramsAt μ a).Kl)⁻¹ * (paramsAt μ a).d ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg (by positivity) (1 : ℝ), Real.rpow_one, mul_inv]
    congr 1
    rw [show (paramsAt μ a).d ^ (-(2 : ℝ)) = ((paramsAt μ a).d ^ 2)⁻¹ by
      rw [Real.rpow_neg (le_of_lt hd) (2 : ℝ), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast]]
  have h2 : (μ * a) ^ (-(1 / 2 : ℝ)) * Real.sqrt (μ * a) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hμa,
      show -(1 / 2 : ℝ) + 1 / 2 = 0 by norm_num, Real.rpow_zero]
  rw [h1]
  rw [show (paramsAt μ a).Kl * (μ * a) ^ (-(1 / 2 : ℝ))
        * (((paramsAt μ a).Kl)⁻¹ * (paramsAt μ a).d ^ (-(2 : ℝ)) * Real.sqrt (μ * a))
      = ((paramsAt μ a).Kl * ((paramsAt μ a).Kl)⁻¹) * (paramsAt μ a).d ^ (-(2 : ℝ))
        * ((μ * a) ^ (-(1 / 2 : ℝ)) * Real.sqrt (μ * a)) by ring]
  rw [h2, mul_one, mul_inv_cancel₀ (ne_of_gt hKl), one_mul]

theorem one_le_honCutRad (v : E3 → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (ht : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1) :
    1 ≤ honCutRad v μ := by
  set a := _root_.BoseGases.a v with ha
  have ht0 : 0 < μ * a ^ 3 := by positivity
  rw [honCutRad_eq_d v μ hμ hav]
  have hd0 : 0 < (paramsAt μ a).d := fsXp_pos (c := 6) ht0
  have hd1 : (paramsAt μ a).d ≤ 1 := by
    have h : (paramsAt μ a).d = fsXp (μ * a ^ 3) 6 := rfl
    rw [h]
    exact fsXp_le_one ht0 ht (by norm_num)
  rw [Real.rpow_neg (le_of_lt hd0) (2 : ℝ)]
  refine (one_le_inv₀ (by positivity : (0 : ℝ) < (paramsAt μ a).d ^ (2 : ℝ))).mpr ?_
  have h2 : (paramsAt μ a).d ^ (2 : ℝ) = (paramsAt μ a).d ^ 2 := Real.rpow_natCast _ 2
  rw [h2]
  nlinarith [hd1, hd0]

/-! ## 3. The `f_L`-mask as a function of the lattice label -/

theorem fL_eq_lab (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (i : Lab (HM μ).N) :
    (honE v h fc fu HM μ).fL i
      = fc.f (‖Work.BoseB4.vec (labVec (HM μ).N i)‖ / honCutRad v μ) := by
  rw [honE_fL_eq HM μ i]
  congr 1
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have h1 : Work.BoseB4.vec (labVec (HM μ).N i) = ellH v μ • (honF v h fc fu HM μ).kmom i := by
    rw [show (honF v h fc fu HM μ).kmom = kmomLab (ellH v μ) (HM μ).N from rfl]
    exact (smul_kmomLab_eq (ne_of_gt hℓ) (HM μ).N i).symm
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ, honCutRad]
  field_simp

theorem fL_ne_zero_le (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) {i : Lab (HM μ).N}
    (hi : (honE v h fc fu HM μ).fL i ≠ 0) :
    ‖Work.BoseB4.vec (labVec (HM μ).N i)‖ ≤ 2 * honCutRad v μ := by
  by_contra hcon
  rw [not_le] at hcon
  rw [fL_eq_lab HM μ hμ hav i] at hi
  have hκ : 0 < honCutRad v μ := honCutRad_pos hav hμ
  have h2 : 2 ≤ ‖Work.BoseB4.vec (labVec (HM μ).N i)‖ / honCutRad v μ := by
    rw [le_div_iff₀ hκ]
    linarith
  exact hi (fc.zero _ h2)

/-! ## 4. Cauchy–Schwarz for `gram`, and Bessel -/

theorem gram_cauchy {m : ℕ} (a b : Fin m → ℝ) :
    |gram a b| ≤ Real.sqrt (gram a a) * Real.sqrt (gram b b) := by
  have ha : 0 ≤ gram a a := by
    simp only [gram]
    exact Finset.sum_nonneg fun l _ => mul_self_nonneg _
  have h1 : (gram a b) ^ 2 ≤ gram a a * gram b b := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
    have h2 : (∑ l : Fin m, a l ^ 2) = gram a a := by
      rw [gram]
      exact Finset.sum_congr rfl fun l _ => by rw [pow_two]
    have h3 : (∑ l : Fin m, b l ^ 2) = gram b b := by
      rw [gram]
      exact Finset.sum_congr rfl fun l _ => by rw [pow_two]
    rw [← h2, ← h3]
    simpa only [gram] using h
  calc |gram a b| = Real.sqrt ((gram a b) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (gram a a * gram b b) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt (gram a a) * Real.sqrt (gram b b) := Real.sqrt_mul ha _

theorem bessel_coord (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ) :
    (∑ i ∈ excited (Lab (HM μ).N), (gcoord HM μ u i) ^ 2) ≤ ∑ l : Fin (HM μ).m, (u l) ^ 2 := by
  have h := sq_decomp HM μ u
  have hz : 0 ≤ ∑ l : Fin (HM μ).m, (zvec HM μ u l) ^ 2 :=
    Finset.sum_nonneg fun l _ => sq_nonneg _
  linarith

/-! ## 5. The lattice-Parseval split of `GchiA` -/

theorem GchiA_split (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v)
    (hN : 2 * honCutRad v μ / Real.pi ≤ ((HM μ).N : ℝ)) (u : Fin (HM μ).m → ℝ) :
    (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
        u l * GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l' * u l')
      = (∑ k : Lab (HM μ).N, (bfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k) ^ 2)
        + ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
            wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i
              * wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u j
              * Tail (HM μ).N i j := by
  set w : Lab (HM μ).N → ℝ := wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u with hw
  set b : Lab (HM μ).N → ℝ := bfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u with hb
  have hMc : ∀ i j : Lab (HM μ).N, Mc (HM μ).N i j
      = (∑ k : Lab (HM μ).N, Chat (HM μ).N k i * Chat (HM μ).N k j) + Tail (HM μ).N i j := by
    intro i j
    rw [Tail]
    ring
  have hgoal : (∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N, w i * w j * Mc (HM μ).N i j)
      = (∑ k : Lab (HM μ).N, (b k) ^ 2)
        + ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N, w i * w j * Tail (HM μ).N i j := by
    have hsplit : (∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N, w i * w j * Mc (HM μ).N i j)
        = (∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
            w i * w j * (∑ k : Lab (HM μ).N, Chat (HM μ).N k i * Chat (HM μ).N k j))
          + ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N, w i * w j * Tail (HM μ).N i j := by
      simp only [hMc, mul_add, Finset.sum_add_distrib]
    have hRHS : (∑ k : Lab (HM μ).N, (b k) ^ 2)
        = ∑ k : Lab (HM μ).N, ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
            w i * w j * (Chat (HM μ).N k i * Chat (HM μ).N k j) := by
      have hpt : ∀ k : Lab (HM μ).N,
          (∑ i : Lab (HM μ).N, w i * Chat (HM μ).N k i)
              * (∑ j : Lab (HM μ).N, w j * Chat (HM μ).N k j)
            = ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
                w i * w j * (Chat (HM μ).N k i * Chat (HM μ).N k j) := by
        intro k
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hb, bfun, ← hw, pow_two]
      exact hpt k
    have hLHS : (∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
          w i * w j * (∑ k : Lab (HM μ).N, Chat (HM μ).N k i * Chat (HM μ).N k j))
        = ∑ k : Lab (HM μ).N, ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
            w i * w j * (Chat (HM μ).N k i * Chat (HM μ).N k j) := by
      simp only [Finset.mul_sum]
      rw [triple_sum_comm]
      try rfl
    rw [hsplit, hLHS, hRHS]
  rw [form_GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ hμ hav hN u]
  rw [hw, hb] at hgoal
  exact hgoal

/-! ## 6. The commutator split of `bfun` -/

/-- The χ-transform of the θ-coordinates, over the excited labels. -/
noncomputable def vt (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ)
    (k : Lab (HM μ).N) : ℝ :=
  ∑ i ∈ excited (Lab (HM μ).N), gcoord HM μ u i * Chat (HM μ).N k i

/-- The commutator `r = [χ, f_L(D)]c`. -/
noncomputable def rt (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ)
    (k : Lab (HM μ).N) : ℝ :=
  ∑ i ∈ excited (Lab (HM μ).N),
    (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N i)‖ / honCutRad v μ)
      - fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / honCutRad v μ))
      * gcoord HM μ u i * Chat (HM μ).N k i

theorem bfun_split (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (u : Fin (HM μ).m → ℝ) (k : Lab (HM μ).N) :
    bfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k
      = fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / honCutRad v μ)
          * vt HM μ u k
        + rt (fc := fc) HM μ u k := by
  rw [bfun]
  have h1 : ∀ i : Lab (HM μ).N,
      wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i * Chat (HM μ).N k i
        = (if i ∈ excited (Lab (HM μ).N) then
            (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N i)‖ / honCutRad v μ)
              * gcoord HM μ u i) * Chat (HM μ).N k i else 0) := by
    intro i
    rw [wfun]
    split_ifs with hmem
    · rw [fL_eq_lab HM μ hμ hav i]
    · rw [zero_mul]
  simp only [h1]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rw [vt, rt, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-! ## 7. The `χ`-content of a χ-mode against the θ-fibre -/

theorem gram_f_split (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ)
    (k : Lab (HM μ).N) :
    gram ((HM μ).f k) u
      = vt HM μ u k + gram (hvec HM μ k) (zvec HM μ u) := by
  have hu : u = uP HM μ u + zvec HM μ u := by
    rw [zvec]
    abel
  conv_lhs => rw [hu]
  rw [gram_add_r]
  have h1 : gram ((HM μ).f k) (uP HM μ u) = vt HM μ u k := by
    rw [uP, vt, gram_sum_smul_r]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Work.BoseB4.gram_comm, gram_g_f_eq_chat]
  have h2 : gram ((HM μ).f k) (zvec HM μ u) = gram (hvec HM μ k) (zvec HM μ u) := by
    have hzero : (HM μ).f k = hvec HM μ k
        + ∑ i ∈ excited (Lab (HM μ).N), Chat (HM μ).N k i • (HM μ).g i := by
      funext l
      simp only [hvec, Pi.sub_apply, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      ring
    conv_lhs => rw [hzero]
    rw [gram_add_l, gram_sum_smul_l]
    have hz : (∑ i ∈ excited (Lab (HM μ).N),
        Chat (HM μ).N k i * gram ((HM μ).g i) (zvec HM μ u)) = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [gram_g_zvec HM μ u i hi, mul_zero]
    rw [hz, add_zero]
  rw [h1, h2]

/-! ## 8. The two commutator/deviation estimates -/

theorem comm_bound (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (u : Fin (HM μ).m → ℝ) :
    (∑ k : Lab (HM μ).N, (rt (fc := fc) HM μ u k) ^ 2)
      ≤ (lipC fc * chiS1 / honCutRad v μ) ^ 2
        * ∑ i ∈ excited (Lab (HM μ).N), (gcoord HM μ u i) ^ 2 := by
  classical
  set κ := honCutRad v μ with hκdef
  set L : ℝ := lipC fc with hLdef
  have hκ : 0 < κ := honCutRad_pos hav hμ
  have hL0 : 0 ≤ L := lipC_nonneg fc
  have hrow : ∀ k : Lab (HM μ).N,
      (∑ i ∈ excited (Lab (HM μ).N),
          chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)) ≤ chiS1 := by
    intro k
    have h1 : (∑ i ∈ excited (Lab (HM μ).N),
          chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
        ≤ ∑ i : Lab (HM μ).N, chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => chiHatWeight_nonneg _)
    have hinj : Function.Injective
        (fun i : Lab (HM μ).N => labVec (HM μ).N k - labVec (HM μ).N i) := by
      intro a b hab
      exact labVec_inj' (HM μ).N (by
        have h3 := congrArg (fun m : Fin 3 → ℤ => labVec (HM μ).N k - m) hab
        simpa using h3)
    have h2 : (∑ i : Lab (HM μ).N, chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
        ≤ chiS1 := by
      have himg : (∑ i : Lab (HM μ).N,
            chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
          = ∑ n ∈ (Finset.univ.image
              (fun i : Lab (HM μ).N => labVec (HM μ).N k - labVec (HM μ).N i)),
              chiHatWeight n := by
        rw [Finset.sum_image]
        intro a _ b _ hab
        exact hinj hab
      rw [himg]
      exact Summable.sum_le_tsum _
        (fun m _ => chiHatWeight_nonneg m) summable_chiHatWeight
    linarith
  have hcol : ∀ i ∈ excited (Lab (HM μ).N),
      (∑ k : Lab (HM μ).N, chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)) ≤ chiS1 := by
    intro i _
    have hinj : Function.Injective
        (fun k : Lab (HM μ).N => labVec (HM μ).N k - labVec (HM μ).N i) := by
      intro a b hab
      exact labVec_inj' (HM μ).N (by
        have h3 := congrArg (fun m : Fin 3 → ℤ => m + labVec (HM μ).N i) hab
        simpa [sub_add_cancel] using h3)
    have himg : (∑ k : Lab (HM μ).N, chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
        = ∑ n ∈ (Finset.univ.image
            (fun k : Lab (HM μ).N => labVec (HM μ).N k - labVec (HM μ).N i)),
            chiHatWeight n := by
      rw [Finset.sum_image]
      intro a _ b _ hab
      exact hinj hab
    rw [himg]
    exact Summable.sum_le_tsum _
      (fun m _ => chiHatWeight_nonneg m) summable_chiHatWeight
  have hpt : ∀ k : Lab (HM μ).N, (rt (fc := fc) HM μ u k) ^ 2
      ≤ (L / κ) ^ 2 *
          ((∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
            * (∑ i ∈ excited (Lab (HM μ).N),
                chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)
                  * (gcoord HM μ u i) ^ 2)) := by
    intro k
    have habs : |rt (fc := fc) HM μ u k| ≤ (L / κ) *
        ∑ i ∈ excited (Lab (HM μ).N),
          chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) * |gcoord HM μ u i| := by
      rw [rt]
      calc |∑ i ∈ excited (Lab (HM μ).N),
              (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N i)‖ / κ)
                - fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ))
                * gcoord HM μ u i * Chat (HM μ).N k i|
          ≤ ∑ i ∈ excited (Lab (HM μ).N),
              |(fc.f (‖Work.BoseB4.vec (labVec (HM μ).N i)‖ / κ)
                - fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ))
                * gcoord HM μ u i * Chat (HM μ).N k i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ excited (Lab (HM μ).N),
              (L / κ) * (chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)
                * |gcoord HM μ u i|) := by
            refine Finset.sum_le_sum fun i _ => ?_
            have hlip : |fc.f (‖Work.BoseB4.vec (labVec (HM μ).N i)‖ / κ)
                - fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ)|
                ≤ (L / κ) * ‖Work.BoseB4.vec (labVec (HM μ).N k - labVec (HM μ).N i)‖ := by
              have h2 := abs_sub_le_lipC fc (‖Work.BoseB4.vec (labVec (HM μ).N i)‖ / κ)
                (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ)
              have h4 : |‖Work.BoseB4.vec (labVec (HM μ).N i)‖
                  - ‖Work.BoseB4.vec (labVec (HM μ).N k)‖|
                  ≤ ‖Work.BoseB4.vec (labVec (HM μ).N k - labVec (HM μ).N i)‖ := by
                rw [vec_sub']
                exact le_trans (abs_norm_sub_norm_le _ _) (le_of_eq (norm_sub_rev _ _))
              have h2' : |fc.f (‖Work.BoseB4.vec (labVec (HM μ).N i)‖ / κ)
                  - fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ)|
                  ≤ L * |‖Work.BoseB4.vec (labVec (HM μ).N i)‖
                      - ‖Work.BoseB4.vec (labVec (HM μ).N k)‖| / κ := by
                convert h2 using 2
                rw [div_sub_div_same, abs_div, abs_of_pos hκ]
                ring
              rw [le_div_iff₀ hκ] at h2'
              rw [div_mul_eq_mul_div, le_div_iff₀ hκ]
              nlinarith [h2', h4, hL0]
            have hChat : |Chat (HM μ).N k i|
                = |chiHat (Work.BoseB4.vec (labVec (HM μ).N k - labVec (HM μ).N i))| := rfl
            calc |(fc.f (‖Work.BoseB4.vec (labVec (HM μ).N i)‖ / κ)
                  - fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ))
                  * gcoord HM μ u i * Chat (HM μ).N k i|
                = |fc.f (‖Work.BoseB4.vec (labVec (HM μ).N i)‖ / κ)
                    - fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ)|
                  * |gcoord HM μ u i| * |Chat (HM μ).N k i| := by rw [abs_mul, abs_mul]
              _ ≤ ((L / κ) * ‖Work.BoseB4.vec (labVec (HM μ).N k - labVec (HM μ).N i)‖)
                  * |gcoord HM μ u i|
                  * |chiHat (Work.BoseB4.vec (labVec (HM μ).N k - labVec (HM μ).N i))| := by
                  rw [hChat]
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hlip (abs_nonneg _)) (abs_nonneg _)
              _ = (L / κ) * (chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)
                    * |gcoord HM μ u i|) := by
                  rw [chiHatWeight]
                  ring
        _ = (L / κ) * ∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) * |gcoord HM μ u i| := by
            rw [Finset.mul_sum]
    have hcs : (∑ i ∈ excited (Lab (HM μ).N),
          chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) * |gcoord HM μ u i|) ^ 2
        ≤ (∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
            * (∑ i ∈ excited (Lab (HM μ).N),
                chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)
                  * (gcoord HM μ u i) ^ 2) := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq (excited (Lab (HM μ).N))
        (fun i => Real.sqrt (chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)))
        (fun i => Real.sqrt (chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
          * |gcoord HM μ u i|)
      have e1 : (∑ i ∈ excited (Lab (HM μ).N),
            Real.sqrt (chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
              * (Real.sqrt (chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
                * |gcoord HM μ u i|))
          = ∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) * |gcoord HM μ u i| := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← mul_assoc, ← pow_two, Real.sq_sqrt (chiHatWeight_nonneg _)]
        try rfl
      have e2 : (∑ i ∈ excited (Lab (HM μ).N),
            (Real.sqrt (chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))) ^ 2)
          = ∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) :=
        Finset.sum_congr rfl fun i _ => Real.sq_sqrt (chiHatWeight_nonneg _)
      have e3 : (∑ i ∈ excited (Lab (HM μ).N),
            (Real.sqrt (chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
              * |gcoord HM μ u i|) ^ 2)
          = ∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) * (gcoord HM μ u i) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, Real.sq_sqrt (chiHatWeight_nonneg _), sq_abs]
        try rfl
      rwa [e1, e2, e3] at h
    have hsq : (rt (fc := fc) HM μ u k) ^ 2
        ≤ ((L / κ) * ∑ i ∈ excited (Lab (HM μ).N),
            chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) * |gcoord HM μ u i|) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg (mul_nonneg (div_nonneg hL0 (le_of_lt hκ))
        (Finset.sum_nonneg fun i _ => mul_nonneg (chiHatWeight_nonneg _) (abs_nonneg _)))]
      exact habs
    calc (rt (fc := fc) HM μ u k) ^ 2
        ≤ ((L / κ) * ∑ i ∈ excited (Lab (HM μ).N),
            chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) * |gcoord HM μ u i|) ^ 2 := hsq
      _ = (L / κ) ^ 2 * (∑ i ∈ excited (Lab (HM μ).N),
            chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) * |gcoord HM μ u i|) ^ 2 := by
          rw [mul_pow]
      _ ≤ (L / κ) ^ 2 *
          ((∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
            * (∑ i ∈ excited (Lab (HM μ).N),
                chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)
                  * (gcoord HM μ u i) ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
  have hstep1 : (∑ k : Lab (HM μ).N, (rt (fc := fc) HM μ u k) ^ 2)
      ≤ ∑ k : Lab (HM μ).N, (L / κ) ^ 2 *
          ((∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
            * (∑ i ∈ excited (Lab (HM μ).N),
                chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)
                  * (gcoord HM μ u i) ^ 2)) :=
    Finset.sum_le_sum fun k _ => hpt k
  have hSnn : ∀ k : Lab (HM μ).N, 0 ≤ ∑ i ∈ excited (Lab (HM μ).N),
      chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) * (gcoord HM μ u i) ^ 2 :=
    fun k => Finset.sum_nonneg fun i _ => mul_nonneg (chiHatWeight_nonneg _) (sq_nonneg _)
  have hX : (∑ k : Lab (HM μ).N, (∑ i ∈ excited (Lab (HM μ).N),
          chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) * (gcoord HM μ u i) ^ 2))
      ≤ chiS1 * ∑ i ∈ excited (Lab (HM μ).N), (gcoord HM μ u i) ^ 2 := by
    have hswap : (∑ k : Lab (HM μ).N, (∑ i ∈ excited (Lab (HM μ).N),
            chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i) * (gcoord HM μ u i) ^ 2))
        = ∑ i ∈ excited (Lab (HM μ).N), (∑ k : Lab (HM μ).N,
            chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
              * (gcoord HM μ u i) ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_mul]
    rw [hswap]
    calc (∑ i ∈ excited (Lab (HM μ).N),
          (∑ k : Lab (HM μ).N, chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
            * (gcoord HM μ u i) ^ 2)
        ≤ ∑ i ∈ excited (Lab (HM μ).N), chiS1 * (gcoord HM μ u i) ^ 2 :=
          Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_right (hcol i hi) (sq_nonneg _)
      _ = chiS1 * ∑ i ∈ excited (Lab (HM μ).N), (gcoord HM μ u i) ^ 2 := by
          rw [Finset.mul_sum]
  have h1 : (∑ k : Lab (HM μ).N, (L / κ) ^ 2 *
        ((∑ i ∈ excited (Lab (HM μ).N),
            chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
          * (∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)
                * (gcoord HM μ u i) ^ 2)))
      ≤ ∑ k : Lab (HM μ).N, (L / κ) ^ 2 *
          (chiS1 * (∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)
                * (gcoord HM μ u i) ^ 2)) :=
    Finset.sum_le_sum fun k _ =>
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hrow k) (hSnn k)) (sq_nonneg _)
  have h1' : (∑ k : Lab (HM μ).N, (L / κ) ^ 2 *
        ((∑ i ∈ excited (Lab (HM μ).N),
            chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
          * (∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)
                * (gcoord HM μ u i) ^ 2)))
      ≤ (L / κ) ^ 2 * (chiS1 * ∑ k : Lab (HM μ).N, (∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)
                * (gcoord HM μ u i) ^ 2)) := by
    refine le_trans h1 (le_of_eq ?_)
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    try rfl
  calc (∑ k : Lab (HM μ).N, (rt (fc := fc) HM μ u k) ^ 2)
      ≤ ∑ k : Lab (HM μ).N, (L / κ) ^ 2 *
          ((∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i))
            * (∑ i ∈ excited (Lab (HM μ).N),
                chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)
                  * (gcoord HM μ u i) ^ 2)) := hstep1
    _ ≤ (L / κ) ^ 2 * (chiS1 * ∑ k : Lab (HM μ).N, (∑ i ∈ excited (Lab (HM μ).N),
              chiHatWeight (labVec (HM μ).N k - labVec (HM μ).N i)
                * (gcoord HM μ u i) ^ 2)) := h1'
    _ ≤ (L / κ) ^ 2 * (chiS1 * (chiS1 * ∑ i ∈ excited (Lab (HM μ).N),
              (gcoord HM μ u i) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX chiS1_nonneg) (sq_nonneg _)
    _ = (L * chiS1 / κ) ^ 2 * ∑ i ∈ excited (Lab (HM μ).N), (gcoord HM μ u i) ^ 2 := by
        rw [hLdef, hκdef]
        ring_nf

theorem tailQuad_bound (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (hR : 1 ≤ rad (HM μ).N (2 * honCutRad v μ))
    (u : Fin (HM μ).m → ℝ) :
    (∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
        wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i
          * wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u j
          * Tail (HM μ).N i j)
      ≤ tailQ * (Fintype.card (Lab (HM μ).N) : ℝ) / rad (HM μ).N (2 * honCutRad v μ) ^ 101
          * ∑ l : Fin (HM μ).m, (u l) ^ 2 := by
  have hL : 0 ≤ 2 * honCutRad v μ := by linarith [le_of_lt (honCutRad_pos hav hμ)]
  have hsupp : ∀ i : Lab (HM μ).N, wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i ≠ 0 →
      ‖Work.BoseB4.vec (labVec (HM μ).N i)‖ ≤ 2 * honCutRad v μ :=
    fun i hi => wfun_norm_le (v := v) (h := h) (fc := fc) (fu := fu) HM μ hμ hav u hi
  have h1 := tailQ_spec (HM μ).N (2 * honCutRad v μ) hL hR
    (wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u) hsupp
  have h2 : (∑ i : Lab (HM μ).N,
      (wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i) ^ 2)
      ≤ ∑ l : Fin (HM μ).m, (u l) ^ 2 := by
    rw [wfun_sq_sum]
    refine le_trans (Finset.sum_le_sum fun i hi => ?_) (bessel_coord HM μ u)
    have hf0 : 0 ≤ (honE v h fc fu HM μ).fL i := LowCut.nonneg fc _
    have hf1 : (honE v h fc fu HM μ).fL i ≤ 1 := LowCut.le_one fc _
    have hf2 : ((honE v h fc fu HM μ).fL i) ^ 2 ≤ 1 := by nlinarith
    calc (((honE v h fc fu HM μ).fL i * gcoord HM μ u i) ^ 2)
        = ((honE v h fc fu HM μ).fL i) ^ 2 * (gcoord HM μ u i) ^ 2 := by ring
      _ ≤ 1 * (gcoord HM μ u i) ^ 2 := mul_le_mul_of_nonneg_right hf2 (sq_nonneg _)
      _ = (gcoord HM μ u i) ^ 2 := by ring
  calc (∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
        wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i
          * wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u j
          * Tail (HM μ).N i j)
      ≤ tailQ * (Fintype.card (Lab (HM μ).N) : ℝ) / rad (HM μ).N (2 * honCutRad v μ) ^ 101
          * (∑ i : Lab (HM μ).N, (wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i) ^ 2) := h1
    _ ≤ tailQ * (Fintype.card (Lab (HM μ).N) : ℝ) / rad (HM μ).N (2 * honCutRad v μ) ^ 101
          * ∑ l : Fin (HM μ).m, (u l) ^ 2 := by
        refine mul_le_mul_of_nonneg_left h2 ?_
        exact div_nonneg (mul_nonneg tailQ_nonneg (Nat.cast_nonneg _))
          (pow_nonneg (by linarith [hR]) 101)

/-- The scalar form of Young's inequality used to pass from the `√`-bound to the `ε`-form. -/
theorem young_sqrt {F μ ε : ℝ} (hF : 0 ≤ F) (hμ : 0 ≤ μ) (hε : 0 < ε) :
    (Real.sqrt F + μ) ^ 2 ≤ (1 + ε) * F + (1 + 1 / ε) * μ ^ 2 := by
  have hsF : Real.sqrt F ^ 2 = F := Real.sq_sqrt hF
  have h1 : 2 * (ε * Real.sqrt F) * μ ≤ (ε * Real.sqrt F) ^ 2 + μ ^ 2 :=
    two_mul_le_add_sq _ _
  have hε2 : (ε * Real.sqrt F) ^ 2 = ε ^ 2 * F := by rw [mul_pow, hsF]
  have h2 : 2 * Real.sqrt F * μ ≤ ε * F + μ ^ 2 / ε := by
    have h3 : (2 * Real.sqrt F * μ) * ε ≤ (ε * F + μ ^ 2 / ε) * ε := by
      have he : (ε * F + μ ^ 2 / ε) * ε = ε ^ 2 * F + μ ^ 2 := by
        field_simp <;> ring
      rw [he]
      nlinarith [h1, hε2]
    exact le_of_mul_le_mul_right h3 hε
  have he : (1 + 1 / ε) * μ ^ 2 = μ ^ 2 + μ ^ 2 / ε := by
    field_simp <;> ring
  rw [he]
  nlinarith [hsF, h2]

/-- Minkowski in `ℓ²` over a finite set. -/
lemma finset_sum_sq_add_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    (∑ i ∈ s, (a i + b i) ^ 2)
      ≤ (Real.sqrt (∑ i ∈ s, (a i) ^ 2) + Real.sqrt (∑ i ∈ s, (b i) ^ 2)) ^ 2 := by
  have ha0 : 0 ≤ ∑ i ∈ s, (a i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hb0 : 0 ≤ ∑ i ∈ s, (b i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hab : (∑ i ∈ s, a i * b i)
      ≤ Real.sqrt (∑ i ∈ s, (a i) ^ 2) * Real.sqrt (∑ i ∈ s, (b i) ^ 2) := by
    have h1 : (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑ i ∈ s, (a i) ^ 2) * ∑ i ∈ s, (b i) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s a b
    calc (∑ i ∈ s, a i * b i) ≤ Real.sqrt ((∑ i ∈ s, a i * b i) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
          exact le_abs_self _
      _ ≤ Real.sqrt ((∑ i ∈ s, (a i) ^ 2) * ∑ i ∈ s, (b i) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (∑ i ∈ s, (a i) ^ 2) * Real.sqrt (∑ i ∈ s, (b i) ^ 2) := Real.sqrt_mul ha0 _
  have h1 : (∑ i ∈ s, (a i + b i) ^ 2)
      = (∑ i ∈ s, (a i) ^ 2) + 2 * (∑ i ∈ s, a i * b i) + (∑ i ∈ s, (b i) ^ 2) := by
    rw [show (∑ i ∈ s, (a i + b i) ^ 2)
        = ∑ i ∈ s, ((a i) ^ 2 + 2 * (a i * b i) + (b i) ^ 2) from
      Finset.sum_congr rfl fun i _ => by ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [show (∑ i ∈ s, 2 * (a i * b i)) = 2 * ∑ i ∈ s, a i * b i by
      rw [Finset.mul_sum]]
    try ring
  have hsq1 : Real.sqrt (∑ i ∈ s, (a i) ^ 2) ^ 2 = ∑ i ∈ s, (a i) ^ 2 := Real.sq_sqrt ha0
  have hsq2 : Real.sqrt (∑ i ∈ s, (b i) ^ 2) ^ 2 = ∑ i ∈ s, (b i) ^ 2 := Real.sq_sqrt hb0
  nlinarith [h1, hab, hsq1, hsq2,
    Real.sqrt_nonneg (∑ i ∈ s, (a i) ^ 2), Real.sqrt_nonneg (∑ i ∈ s, (b i) ^ 2)]

/-- Minkowski in `ℓ²`: the square-sum of a sum is at most the square of the sum of the
square-roots of the square-sums. -/
lemma sum_sq_add_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    (∑ i, (a i + b i) ^ 2)
      ≤ (Real.sqrt (∑ i, (a i) ^ 2) + Real.sqrt (∑ i, (b i) ^ 2)) ^ 2 := by
  have ha0 : 0 ≤ ∑ i, (a i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hb0 : 0 ≤ ∑ i, (b i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hab : (∑ i, a i * b i) ≤ Real.sqrt (∑ i, (a i) ^ 2) * Real.sqrt (∑ i, (b i) ^ 2) := by
    have h1 : (∑ i, a i * b i) ^ 2 ≤ (∑ i, (a i) ^ 2) * ∑ i, (b i) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
    calc (∑ i, a i * b i) ≤ Real.sqrt ((∑ i, a i * b i) ^ 2) := by
          rw [Real.sqrt_sq_eq_abs]
          exact le_abs_self _
      _ ≤ Real.sqrt ((∑ i, (a i) ^ 2) * ∑ i, (b i) ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt (∑ i, (a i) ^ 2) * Real.sqrt (∑ i, (b i) ^ 2) := Real.sqrt_mul ha0 _
  have h1 : (∑ i, (a i + b i) ^ 2)
      = (∑ i, (a i) ^ 2) + 2 * (∑ i, a i * b i) + (∑ i, (b i) ^ 2) := by
    rw [show (∑ i, (a i + b i) ^ 2)
        = ∑ i, ((a i) ^ 2 + 2 * (a i * b i) + (b i) ^ 2) from
      Finset.sum_congr rfl fun i _ => by ring]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    try ring
  have hsq1 : Real.sqrt (∑ i, (a i) ^ 2) ^ 2 = ∑ i, (a i) ^ 2 := Real.sq_sqrt ha0
  have hsq2 : Real.sqrt (∑ i, (b i) ^ 2) ^ 2 = ∑ i, (b i) ^ 2 := Real.sq_sqrt hb0
  nlinarith [h1, hab, hsq1, hsq2,
    Real.sqrt_nonneg (∑ i, (a i) ^ 2), Real.sqrt_nonneg (∑ i, (b i) ^ 2)]

/-- The deviation root times `κ` is bounded by the diluted constant `√(27tailE/2¹⁰¹)`. -/
lemma devRoot_mul_le {κ rad : ℝ} (hκ : 1 ≤ κ) (hκ0 : 0 < κ) (hrad : 2 * κ ≤ rad) :
    Real.sqrt (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad ^ 101) * κ
      ≤ Real.sqrt (27 * tailE) := by
  have hrad0 : 0 < rad := lt_of_lt_of_le (by positivity) hrad
  have htE : 0 ≤ tailE := tailE_nonneg
  have hA0 : 0 ≤ tailE * (2 * κ / Real.pi + 1) ^ 3 / rad ^ 101 := by positivity
  have hstep1 : (2 * κ / Real.pi + 1) ^ 3 ≤ 27 * κ ^ 3 := by
    have hpi : 2 / Real.pi ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [Real.pi_gt_three]
    have h1 : 2 * κ / Real.pi + 1 ≤ 3 * κ := by
      have h2 : 2 * κ / Real.pi = (2 / Real.pi) * κ := by ring
      nlinarith [hpi, hκ, h2]
    calc (2 * κ / Real.pi + 1) ^ 3 ≤ (3 * κ) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
      _ = 27 * κ ^ 3 := by ring
  have hstep2 : (2 * κ) ^ 101 ≤ rad ^ 101 := pow_le_pow_left₀ (by positivity) hrad 101
  have hpow : (2 : ℝ) ^ 101 * κ ^ 101 = (2 * κ) ^ 101 := by rw [mul_pow]
  have hκ96 : (1 : ℝ) ≤ 2 ^ 101 * κ ^ 96 := by
    have h1 : (1 : ℝ) ≤ κ ^ 96 := one_le_pow₀ hκ
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ 101 := one_le_pow₀ (by norm_num)
    nlinarith [h1, h2]
  have hkey : tailE * (2 * κ / Real.pi + 1) ^ 3 * κ ^ 2 / rad ^ 101 ≤ 27 * tailE := by
    rw [div_le_iff₀ (pow_pos hrad0 101)]
    have h1 : tailE * (2 * κ / Real.pi + 1) ^ 3 * κ ^ 2 ≤ tailE * (27 * κ ^ 3) * κ ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep1 htE) (sq_nonneg κ)
    have hκp : κ ^ 101 = κ ^ 5 * κ ^ 96 := by rw [← pow_add]
    have h3 : 27 * tailE * κ ^ 5 ≤ 27 * tailE * (2 ^ 101 * κ ^ 96) * κ ^ 5 := by
      have hA : 0 ≤ 27 * tailE * κ ^ 5 :=
        mul_nonneg (mul_nonneg (by norm_num) htE) (pow_nonneg (le_of_lt hκ0) 5)
      calc 27 * tailE * κ ^ 5 = (27 * tailE * κ ^ 5) * 1 := by ring
        _ ≤ (27 * tailE * κ ^ 5) * (2 ^ 101 * κ ^ 96) := mul_le_mul_of_nonneg_left hκ96 hA
        _ = 27 * tailE * (2 ^ 101 * κ ^ 96) * κ ^ 5 := by ring
    have h4 : 27 * tailE * (2 ^ 101 * κ ^ 96) * κ ^ 5 = 27 * tailE * (2 * κ) ^ 101 := by
      rw [mul_pow, hκp]
      ring
    have h5 : 27 * tailE * (2 * κ) ^ 101 ≤ 27 * tailE * rad ^ 101 :=
      mul_le_mul_of_nonneg_left hstep2 (mul_nonneg (by norm_num) htE)
    linarith [h1, h3, h4, h5]
  have hgoal : (Real.sqrt (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad ^ 101) * κ) ^ 2
      ≤ (Real.sqrt (27 * tailE)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hA0, Real.sq_sqrt (by positivity)]
    rw [show tailE * (2 * κ / Real.pi + 1) ^ 3 / rad ^ 101 * κ ^ 2
        = tailE * (2 * κ / Real.pi + 1) ^ 3 * κ ^ 2 / rad ^ 101 by ring]
    exact hkey
  calc Real.sqrt (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad ^ 101) * κ
      = Real.sqrt ((Real.sqrt (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad ^ 101) * κ) ^ 2) :=
        (Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hκ0))).symm
    _ ≤ Real.sqrt ((Real.sqrt (27 * tailE)) ^ 2) := Real.sqrt_le_sqrt hgoal
    _ = Real.sqrt (27 * tailE) := Real.sqrt_sq (Real.sqrt_nonneg _)

/-- The `Tail` root is bounded by `√(27 tailQ / π¹⁰¹)`. -/
lemma tailRoot_le {rad N : ℝ} (hN1 : 1 ≤ N) (hrad3 : Real.pi * N ≤ rad) :
    Real.sqrt (tailQ * (2 * N + 1) ^ 3 / rad ^ 101)
      ≤ Real.sqrt (27 * tailQ / Real.pi ^ 101) := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hrad0 : 0 < rad := lt_of_lt_of_le (by positivity) hrad3
  have htQ : 0 ≤ tailQ := tailQ_nonneg
  have hA0 : 0 ≤ tailQ * (2 * N + 1) ^ 3 / rad ^ 101 := by positivity
  have hnum : (2 * N + 1) ^ 3 ≤ 27 * N ^ 3 := by
    have h1 : 2 * N + 1 ≤ 3 * N := by linarith
    calc (2 * N + 1) ^ 3 ≤ (3 * N) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
      _ = 27 * N ^ 3 := by ring
  have hden : (Real.pi * N) ^ 101 ≤ rad ^ 101 := pow_le_pow_left₀ (by positivity) hrad3 101
  have hpow : (Real.pi * N) ^ 101 = Real.pi ^ 101 * N ^ 101 := by rw [mul_pow]
  have hN101 : N ^ 3 ≤ N ^ 101 := by
    have h1 : (1 : ℝ) ≤ N ^ 98 := one_le_pow₀ hN1
    calc N ^ 3 = N ^ 3 * 1 := by ring
      _ ≤ N ^ 3 * N ^ 98 := mul_le_mul_of_nonneg_left h1 (pow_nonneg (le_of_lt hN0) 3)
      _ = N ^ 101 := by rw [← pow_add]
  have hkey : tailQ * (2 * N + 1) ^ 3 / rad ^ 101 ≤ 27 * tailQ / Real.pi ^ 101 := by
    rw [div_le_iff₀ (pow_pos hrad0 101), div_mul_eq_mul_div,
      le_div_iff₀ (pow_pos Real.pi_pos 101)]
    have h1 : tailQ * (2 * N + 1) ^ 3 ≤ tailQ * (27 * N ^ 3) :=
      mul_le_mul_of_nonneg_left hnum htQ
    have h2 : tailQ * (27 * N ^ 3) * Real.pi ^ 101 ≤ tailQ * (27 * N ^ 101) * Real.pi ^ 101 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hN101 (by norm_num)) htQ) (pow_nonneg Real.pi_pos.le 101)
    have hNp : N ^ 101 = N ^ 3 * N ^ 98 := by rw [← pow_add]
    have h4 : tailQ * (27 * N ^ 101) * Real.pi ^ 101 = 27 * tailQ * (Real.pi * N) ^ 101 := by
      rw [hpow, hNp]
      ring
    have h5 : 27 * tailQ * (Real.pi * N) ^ 101 ≤ 27 * tailQ * rad ^ 101 :=
      mul_le_mul_of_nonneg_left hden (by positivity)
    have h1' : tailQ * (2 * N + 1) ^ 3 * Real.pi ^ 101 ≤ tailQ * (27 * N ^ 3) * Real.pi ^ 101 :=
      mul_le_mul_of_nonneg_right h1 (pow_nonneg Real.pi_pos.le 101)
    linarith [h1', h2, h4, h5]
  have hgoal : (Real.sqrt (tailQ * (2 * N + 1) ^ 3 / rad ^ 101)) ^ 2
      ≤ (Real.sqrt (27 * tailQ / Real.pi ^ 101)) ^ 2 := by
    rw [Real.sq_sqrt hA0, Real.sq_sqrt (by positivity)]
    exact hkey
  calc Real.sqrt (tailQ * (2 * N + 1) ^ 3 / rad ^ 101)
      = Real.sqrt ((Real.sqrt (tailQ * (2 * N + 1) ^ 3 / rad ^ 101)) ^ 2) :=
        (Real.sqrt_sq (Real.sqrt_nonneg _)).symm
    _ ≤ Real.sqrt ((Real.sqrt (27 * tailQ / Real.pi ^ 101)) ^ 2) := Real.sqrt_le_sqrt hgoal
    _ = Real.sqrt (27 * tailQ / Real.pi ^ 101) := Real.sqrt_sq (Real.sqrt_nonneg _)

/-- **The diagonal `Tail`-mass of the low band.**  Every lattice label whose profile value
`f_L(K_k/κ)` does not vanish has momentum in the ball of radius `2κ` (`fL_ne_zero_le`); there are
at most `(2κ/π+1)³` such labels (`Work.BoseK15.card_le_of_vec_norm_le`), and each contributes at
most `tailE/rad^101` to the diagonal of `Tail` (`tailIdentity` + `tailE_spec`). -/
theorem dev_bound (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v)
    (hR : 1 ≤ rad (HM μ).N (2 * honCutRad v μ)) :
    (∑ k ∈ Finset.univ.filter (fun k : Lab (HM μ).N =>
        fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / honCutRad v μ) ≠ 0),
        Tail (HM μ).N k k)
      ≤ tailE * (2 * honCutRad v μ / Real.pi + 1) ^ 3
          / rad (HM μ).N (2 * honCutRad v μ) ^ 101 := by
  classical
  set S : Finset (Lab (HM μ).N) := Finset.univ.filter (fun k : Lab (HM μ).N =>
      fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / honCutRad v μ) ≠ 0) with hS
  have hκ : 0 < honCutRad v μ := honCutRad_pos hav hμ
  have hL : 0 ≤ 2 * honCutRad v μ := by positivity
  have hrad0 : 0 < rad (HM μ).N (2 * honCutRad v μ) := lt_of_lt_of_le zero_lt_one hR
  have hR' : 1 ≤ 2 * Real.pi * (((HM μ).N : ℝ) + 1) - 2 * honCutRad v μ := hR
  have hnorm : ∀ k : Lab (HM μ).N, k ∈ S →
      ‖Work.BoseB4.vec (labVec (HM μ).N k)‖ ≤ 2 * honCutRad v μ := by
    intro k hk
    have hk' : fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / honCutRad v μ) ≠ 0 :=
      (Finset.mem_filter.mp hk).2
    by_contra hcon
    rw [not_le] at hcon
    have h2 : 2 ≤ ‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / honCutRad v μ := by
      rw [le_div_iff₀ hκ]
      linarith
    exact hk' (fc.zero _ h2)
  have hentry : ∀ k : Lab (HM μ).N, k ∈ S →
      Tail (HM μ).N k k ≤ tailE / rad (HM μ).N (2 * honCutRad v μ) ^ 101 := by
    intro k hk
    have hk' : ‖Work.BoseB4.vec (labVec (HM μ).N k)‖ ≤ 2 * honCutRad v μ := hnorm k hk
    rw [tailIdentity (HM μ).N k k]
    exact le_trans (le_abs_self _)
      (tailE_spec (HM μ).N (2 * honCutRad v μ) hL hR' (labVec (HM μ).N k)
        (labVec (HM μ).N k) hk' hk')
  have hcard : (S.card : ℝ) ≤ (2 * honCutRad v μ / Real.pi + 1) ^ 3 := by
    have himg : (S.image (labVec (HM μ).N)).card = S.card :=
      Finset.card_image_of_injective _ (labVec_inj' (HM μ).N)
    have hcount : ((S.image (labVec (HM μ).N)).card : ℝ)
        ≤ (2 * honCutRad v μ / Real.pi + 1) ^ 3 := by
      refine Work.BoseK15.card_le_of_vec_norm_le _ (2 * honCutRad v μ) hL ?_
      intro n hn
      obtain ⟨k, hk, hkn⟩ := Finset.mem_image.mp hn
      rw [← hkn]
      exact hnorm k hk
    rwa [himg] at hcount
  have hsum : (∑ k ∈ S, Tail (HM μ).N k k)
      ≤ ∑ k ∈ S, tailE / rad (HM μ).N (2 * honCutRad v μ) ^ 101 :=
    Finset.sum_le_sum fun k hk => hentry k hk
  have hconst : (∑ _k ∈ S, tailE / rad (HM μ).N (2 * honCutRad v μ) ^ 101)
      = (S.card : ℝ) * (tailE / rad (HM μ).N (2 * honCutRad v μ) ^ 101) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcmul : (S.card : ℝ) * (tailE / rad (HM μ).N (2 * honCutRad v μ) ^ 101)
      ≤ (2 * honCutRad v μ / Real.pi + 1) ^ 3
          * (tailE / rad (HM μ).N (2 * honCutRad v μ) ^ 101) :=
    mul_le_mul_of_nonneg_right hcard
      (div_nonneg tailE_nonneg (pow_nonneg hrad0.le 101))
  calc (∑ k ∈ S, Tail (HM μ).N k k)
      ≤ ∑ k ∈ S, tailE / rad (HM μ).N (2 * honCutRad v μ) ^ 101 := hsum
    _ = (S.card : ℝ) * (tailE / rad (HM μ).N (2 * honCutRad v μ) ^ 101) := hconst
    _ ≤ (2 * honCutRad v μ / Real.pi + 1) ^ 3
          * (tailE / rad (HM μ).N (2 * honCutRad v μ) ^ 101) := hcmul
    _ = tailE * (2 * honCutRad v μ / Real.pi + 1) ^ 3
          / rad (HM μ).N (2 * honCutRad v μ) ^ 101 := by ring

/-! ## A. Two arithmetic helpers -/

/-- Cauchy–Schwarz in squared form for the lattice Gram matrix. -/
theorem gram_sq_le {m : ℕ} (a b : Fin m → ℝ) : (gram a b) ^ 2 ≤ gram a a * gram b b := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have h2 : (∑ l : Fin m, a l ^ 2) = gram a a := by
    rw [gram]
    exact Finset.sum_congr rfl fun l _ => by rw [pow_two]
  have h3 : (∑ l : Fin m, b l ^ 2) = gram b b := by
    rw [gram]
    exact Finset.sum_congr rfl fun l _ => by rw [pow_two]
  rw [← h2, ← h3]
  simpa only [gram] using h

/-- `κ² ≤ N⁹⁸` in the dilute régime (`2κ ≤ πN`, `N ≥ 2`). -/
theorem sq_kappa_le_pow (N : ℕ) (κ : ℝ) (hN : 2 ≤ N) (hκ : 1 ≤ κ)
    (h2κ : 2 * κ ≤ Real.pi * (N : ℝ)) : κ ^ 2 ≤ (N : ℝ) ^ 98 := by
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hκ0 : 0 ≤ κ := le_trans zero_le_one hκ
  have hκle : κ ≤ Real.pi * (N : ℝ) / 2 := by linarith
  have h96 : (4 : ℝ) ≤ (N : ℝ) ^ 96 := by
    have h1 : (2 : ℝ) ^ 96 ≤ (N : ℝ) ^ 96 := pow_le_pow_left₀ (by norm_num) hN2 96
    have h2 : (4 : ℝ) ≤ (2 : ℝ) ^ 96 := by norm_num
    linarith
  have hpi : Real.pi ^ 2 / 4 ≤ (N : ℝ) ^ 96 := by
    have h3 : Real.pi ^ 2 ≤ 16 := by nlinarith [Real.pi_lt_four, Real.pi_pos]
    linarith
  calc κ ^ 2 ≤ (Real.pi * (N : ℝ) / 2) ^ 2 := pow_le_pow_left₀ hκ0 hκle 2
    _ = Real.pi ^ 2 / 4 * (N : ℝ) ^ 2 := by ring
    _ ≤ (N : ℝ) ^ 96 * (N : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hpi (sq_nonneg _)
    _ = (N : ℝ) ^ 98 := by ring

/-- The `Tail` count: `(2N+1)³/rad(N,2κ)¹⁰¹ ≤ 27/(π¹⁰¹κ²)`. -/
theorem card_div_rad_le (N : ℕ) (κ : ℝ) (hN : 2 ≤ N) (hκ : 1 ≤ κ)
    (h2κ : 2 * κ ≤ Real.pi * (N : ℝ)) :
    ((2 * N + 1) ^ 3 : ℝ) / rad N (2 * κ) ^ 101 ≤ 27 / (Real.pi ^ 101 * κ ^ 2) := by
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hrad : Real.pi * (N : ℝ) ≤ rad N (2 * κ) := by
    rw [rad]
    linarith [h2κ, Real.pi_pos]
  have hrad0 : 0 < rad N (2 * κ) := lt_of_lt_of_le (by positivity) hrad
  have hcore : κ ^ 2 ≤ (N : ℝ) ^ 98 := sq_kappa_le_pow N κ hN hκ h2κ
  have hcard : ((2 * N + 1) ^ 3 : ℝ) ≤ 27 * (N : ℝ) ^ 3 := by
    have hcast : ((2 * N + 1) ^ 3 : ℝ) = (2 * (N : ℝ) + 1) ^ 3 := by push_cast; ring
    rw [hcast]
    have h1 : 2 * (N : ℝ) + 1 ≤ 3 * (N : ℝ) := by
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
      linarith
    calc (2 * (N : ℝ) + 1) ^ 3 ≤ (3 * (N : ℝ)) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
      _ = 27 * (N : ℝ) ^ 3 := by ring
  rw [div_le_div_iff₀ (pow_pos hrad0 101) (by positivity)]
  have hkey : ((2 * N + 1) ^ 3 : ℝ) * (Real.pi ^ 101 * κ ^ 2) ≤ 27 * rad N (2 * κ) ^ 101 := by
    have hcast : ((2 * N + 1) ^ 3 : ℝ) = (2 * (N : ℝ) + 1) ^ 3 := by push_cast; ring
    rw [hcast]
    have h1 : (2 * (N : ℝ) + 1) ^ 3 * (Real.pi ^ 101 * κ ^ 2)
        ≤ (27 * (N : ℝ) ^ 3) * (Real.pi ^ 101 * κ ^ 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    have h2 : (27 * (N : ℝ) ^ 3) * (Real.pi ^ 101 * κ ^ 2)
        ≤ (27 * (N : ℝ) ^ 3) * (Real.pi ^ 101 * (N : ℝ) ^ 98) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcore (by positivity)) (by positivity)
    have h3 : (27 * (N : ℝ) ^ 3) * (Real.pi ^ 101 * (N : ℝ) ^ 98)
        = 27 * Real.pi ^ 101 * (N : ℝ) ^ 101 := by ring
    have h4 : 27 * Real.pi ^ 101 * (N : ℝ) ^ 101 = 27 * (Real.pi * (N : ℝ)) ^ 101 := by
      rw [mul_pow]; ring
    have h5 : 27 * (Real.pi * (N : ℝ)) ^ 101 ≤ 27 * (rad N (2 * κ)) ^ 101 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hrad 101) (by norm_num)
    linarith [h1, h2, h3, h4, h5]
  exact hkey

/-! ## B. The one-body row -/

theorem oneBodyRow (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) (ht : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1)
    (hN : Ng0 v μ ≤ (HM μ).N) (ε : ℝ) (hε : 0 < ε) (u : Fin (HM μ).m → ℝ) :
    (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
        u l * GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l' * u l')
      ≤ (1 + ε) * (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
          u l * GchiF HM μ l l' * u l')
        + (1 + 1 / ε) * (rowC fc / honCutRad v μ) ^ 2 * ∑ l : Fin (HM μ).m, (u l) ^ 2 := by
  classical
  set κ := honCutRad v μ with hκdef
  have hκ1 : 1 ≤ κ := one_le_honCutRad v μ hμ hav ht
  have hκ : 0 < κ := honCutRad_pos hav hμ
  have hKCnn : 0 ≤ lipC fc * chiS1 := mul_nonneg (lipC_nonneg fc) chiS1_nonneg
  have htE : 0 ≤ tailE := tailE_nonneg
  have htQ : 0 ≤ tailQ := tailQ_nonneg
  have hN' : 2 * κ / Real.pi ≤ ((HM μ).N : ℝ) := by
    have h1 := le_Ng0 v μ
    have h2 : (Ng0 v μ : ℝ) ≤ ((HM μ).N : ℝ) := Nat.cast_le.mpr hN
    linarith
  have h2κ : 2 * κ ≤ Real.pi * ((HM μ).N : ℝ) := by
    rw [div_le_iff₀ Real.pi_pos] at hN'
    linarith
  have hNplus : 2 * κ / Real.pi + 1 ≤ ((HM μ).N : ℝ) := by
    have h1 : 2 * κ / Real.pi + 1 ≤ (Ng0 v μ : ℝ) := by
      rw [hκdef]
      exact Nat.le_ceil (2 * honCutRad v μ / Real.pi + 1)
    have h2 : (Ng0 v μ : ℝ) ≤ ((HM μ).N : ℝ) := Nat.cast_le.mpr hN
    linarith
  have hNgt1 : (1 : ℝ) < ((HM μ).N : ℝ) := by
    have h1 : 0 < 2 * κ / Real.pi := div_pos (by linarith) Real.pi_pos
    linarith
  have hN2n : 2 ≤ (HM μ).N := by
    by_contra hcon
    rw [not_le] at hcon
    have h4 : ((HM μ).N : ℝ) ≤ 1 := by
      have h5 : (HM μ).N ≤ 1 := by omega
      exact_mod_cast h5
    linarith
  have hN1 : (1 : ℝ) ≤ ((HM μ).N : ℝ) := le_of_lt hNgt1
  have hN0 : (0 : ℝ) ≤ ((HM μ).N : ℝ) := Nat.cast_nonneg _
  have hrad1 : 1 ≤ rad (HM μ).N (2 * κ) := by
    rw [rad]
    nlinarith [h2κ, Real.pi_gt_three, hN0]
  have hrad2 : 2 * κ ≤ rad (HM μ).N (2 * κ) := by
    rw [rad]
    nlinarith [h2κ, Real.pi_gt_three, hN0]
  have hradP : 0 < rad (HM μ).N (2 * κ) := lt_of_lt_of_le zero_lt_one hrad1
  have hT0 : 0 ≤ tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101 := by
    have hbase : 0 ≤ 2 * κ / Real.pi + 1 := by
      have hh : 0 ≤ 2 * κ / Real.pi := div_nonneg (by linarith) Real.pi_pos.le
      linarith
    exact div_nonneg (mul_nonneg htE (pow_nonneg hbase 3)) (pow_nonneg hradP.le 101)
  have hcomm := comm_bound (v := v) (fc := fc) HM μ hμ hav u
  have htail := tailQuad_bound (v := v) (h := h) (fc := fc) (fu := fu) HM μ hμ hav hrad1 u
  have hdev := dev_bound (v := v) (fc := fc) HM μ hμ hav hrad1
  have hbes := bessel_coord HM μ u
  have hsplit := GchiA_split (v := v) (h := h) (fc := fc) (fu := fu) HM μ hμ hav hN' u
  have hFFeq := form_GchiF HM μ u
  have hUnn : 0 ≤ ∑ l : Fin (HM μ).m, (u l) ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hFFnn : 0 ≤ ∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2 :=
    Finset.sum_nonneg fun k _ => sq_nonneg _
  have hrootU : 0 ≤ Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) := Real.sqrt_nonneg _
  set S : Finset (Lab (HM μ).N) := Finset.univ.filter
      (fun k : Lab (HM μ).N => fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) ≠ 0) with hS
  have hgramnn : ∀ a : Fin (HM μ).m → ℝ, 0 ≤ gram a a := by
    intro a
    simp only [gram]
    exact Finset.sum_nonneg fun l _ => mul_self_nonneg _
  -- (A) the deviation block
  have hdev2 : (∑ k ∈ S, gram (hvec HM μ k) (hvec HM μ k))
      ≤ tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101 := by
    have h1 : ∀ k : Lab (HM μ).N, gram (hvec HM μ k) (hvec HM μ k) = Tail (HM μ).N k k :=
      fun k => hvec_gram (v := v) (h := h) (fc := fc) (fu := fu) HM μ k k
    calc (∑ k ∈ S, gram (hvec HM μ k) (hvec HM μ k))
        = ∑ k ∈ S, Tail (HM μ).N k k := Finset.sum_congr rfl fun k _ => h1 k
      _ ≤ tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101 := hdev
  have hz : gram (zvec HM μ u) (zvec HM μ u) ≤ ∑ l : Fin (HM μ).m, (u l) ^ 2 := by
    have h1 : gram (zvec HM μ u) (zvec HM μ u)
        = ∑ l : Fin (HM μ).m, (zvec HM μ u l) ^ 2 := by
      simp only [gram]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [h1]
    have h2 := sq_decomp HM μ u
    have h3 : 0 ≤ ∑ i ∈ excited (Lab (HM μ).N), (gcoord HM μ u i) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    linarith
  have hdev3 : (∑ k ∈ S, (gram (hvec HM μ k) (zvec HM μ u)) ^ 2)
      ≤ (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101)
        * (∑ l : Fin (HM μ).m, (u l) ^ 2) := by
    have hpt : (∑ k ∈ S, (gram (hvec HM μ k) (zvec HM μ u)) ^ 2)
        ≤ (∑ k ∈ S, gram (hvec HM μ k) (hvec HM μ k))
            * gram (zvec HM μ u) (zvec HM μ u) := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun k _ => gram_sq_le (hvec HM μ k) (zvec HM μ u)
    exact le_trans hpt (mul_le_mul hdev2 hz (hgramnn _) hT0)
  -- (B) the commutator part
  have hRt : Real.sqrt (∑ k : Lab (HM μ).N, (rt (fc := fc) HM μ u k) ^ 2)
      ≤ lipC fc * chiS1 / κ * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) := by
    have h1 : Real.sqrt (∑ k : Lab (HM μ).N, (rt (fc := fc) HM μ u k) ^ 2)
        ≤ Real.sqrt ((lipC fc * chiS1 / κ) ^ 2
            * ∑ i ∈ excited (Lab (HM μ).N), (gcoord HM μ u i) ^ 2) := Real.sqrt_le_sqrt hcomm
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (div_nonneg hKCnn (le_of_lt hκ))] at h1
    exact le_trans h1 (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hbes)
      (div_nonneg hKCnn (le_of_lt hκ)))
  -- (C) the masked `vt`-sum
  have hVtS : (∑ k : Lab (HM μ).N,
        (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) * vt HM μ u k) ^ 2)
      ≤ ∑ k ∈ S, (vt HM μ u k) ^ 2 := by
    have hzero : ∀ k ∈ (Finset.univ : Finset (Lab (HM μ).N)), k ∉ S →
        (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) * vt HM μ u k) ^ 2 = 0 := by
      intro k _ hk
      have hp : ¬ (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) ≠ 0) := by
        intro hcon
        exact hk (by rw [hS]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, hcon⟩)
      have hz0 : fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) = 0 := not_not.mp hp
      simp [hz0]
    have heq : (∑ k : Lab (HM μ).N,
          (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) * vt HM μ u k) ^ 2)
        = ∑ k ∈ S, (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) * vt HM μ u k) ^ 2 :=
      (Finset.sum_subset (Finset.subset_univ S) hzero).symm
    rw [heq]
    refine Finset.sum_le_sum fun k _ => ?_
    have hφ1 : fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) ≤ 1 := LowCut.le_one fc _
    have hφ0 : 0 ≤ fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) := LowCut.nonneg fc _
    have hφ2 : (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ)) ^ 2 ≤ 1 := by nlinarith
    calc (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) * vt HM μ u k) ^ 2
        = (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ)) ^ 2 * (vt HM μ u k) ^ 2 := by ring
      _ ≤ 1 * (vt HM μ u k) ^ 2 := mul_le_mul_of_nonneg_right hφ2 (sq_nonneg _)
      _ = (vt HM μ u k) ^ 2 := by ring
  -- (D) the deviation of `vt`
  have hCS : ∀ k : Lab (HM μ).N, (vt HM μ u k) ^ 2
      ≤ (|gram ((HM μ).f k) u| + |gram (hvec HM μ k) (zvec HM μ u)|) ^ 2 := by
    intro k
    have h2 := gram_f_split HM μ u k
    have h3 : vt HM μ u k = gram ((HM μ).f k) u - gram (hvec HM μ k) (zvec HM μ u) := by
      rw [h2]
      ring
    have h4 : |vt HM μ u k| ≤ |gram ((HM μ).f k) u| + |gram (hvec HM μ k) (zvec HM μ u)| := by
      rw [h3]
      have h5 := abs_sub_le (gram ((HM μ).f k) u) 0 (gram (hvec HM μ k) (zvec HM μ u))
      simpa using h5
    rw [← sq_abs (vt HM μ u k)]
    exact pow_le_pow_left₀ (abs_nonneg _) h4 2
  have hpt : (∑ k ∈ S, (vt HM μ u k) ^ 2)
      ≤ (Real.sqrt (∑ k ∈ S, (gram ((HM μ).f k) u) ^ 2)
          + Real.sqrt (∑ k ∈ S, (gram (hvec HM μ k) (zvec HM μ u)) ^ 2)) ^ 2 := by
    calc (∑ k ∈ S, (vt HM μ u k) ^ 2)
        ≤ ∑ k ∈ S, (|gram ((HM μ).f k) u| + |gram (hvec HM μ k) (zvec HM μ u)|) ^ 2 :=
          Finset.sum_le_sum fun k _ => hCS k
      _ ≤ (Real.sqrt (∑ k ∈ S, (|gram ((HM μ).f k) u|) ^ 2)
            + Real.sqrt (∑ k ∈ S, (|gram (hvec HM μ k) (zvec HM μ u)|) ^ 2)) ^ 2 :=
          finset_sum_sq_add_le S (fun k => |gram ((HM μ).f k) u|)
            (fun k => |gram (hvec HM μ k) (zvec HM μ u)|)
      _ = (Real.sqrt (∑ k ∈ S, (gram ((HM μ).f k) u) ^ 2)
            + Real.sqrt (∑ k ∈ S, (gram (hvec HM μ k) (zvec HM μ u)) ^ 2)) ^ 2 := by
          simp only [sq_abs]
  have hPhiS : (∑ k ∈ S, (gram ((HM μ).f k) u) ^ 2)
      ≤ ∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun k _ _ => sq_nonneg _)
  have hZeta : Real.sqrt (∑ k ∈ S, (gram (hvec HM μ k) (zvec HM μ u)) ^ 2)
      ≤ Real.sqrt (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101)
        * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) := by
    have h1 : Real.sqrt (∑ k ∈ S, (gram (hvec HM μ k) (zvec HM μ u)) ^ 2)
        ≤ Real.sqrt ((tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101)
            * ∑ l : Fin (HM μ).m, (u l) ^ 2) := Real.sqrt_le_sqrt hdev3
    rw [Real.sqrt_mul hT0] at h1
    exact h1
  have hVtS2 : (∑ k ∈ S, (vt HM μ u k) ^ 2)
      ≤ (Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
          + Real.sqrt (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101)
            * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2 := by
    calc (∑ k ∈ S, (vt HM μ u k) ^ 2)
        ≤ (Real.sqrt (∑ k ∈ S, (gram ((HM μ).f k) u) ^ 2)
            + Real.sqrt (∑ k ∈ S, (gram (hvec HM μ k) (zvec HM μ u)) ^ 2)) ^ 2 := hpt
      _ ≤ (Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
            + Real.sqrt (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101)
              * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            (add_le_add (Real.sqrt_le_sqrt hPhiS) hZeta) 2
  -- (E) the `bfun` sum
  have hbf : ∀ k : Lab (HM μ).N, bfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k
      = fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) * vt HM μ u k
        + rt (fc := fc) HM μ u k := fun k =>
    bfun_split (v := v) (h := h) (fc := fc) (fu := fu) HM μ hμ hav u k
  have hbsum : (∑ k : Lab (HM μ).N,
        (bfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k) ^ 2)
      ≤ (Real.sqrt (∑ k : Lab (HM μ).N,
            (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) * vt HM μ u k) ^ 2)
          + Real.sqrt (∑ k : Lab (HM μ).N, (rt (fc := fc) HM μ u k) ^ 2)) ^ 2 := by
    have heq : (∑ k : Lab (HM μ).N,
          (bfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k) ^ 2)
        = ∑ k : Lab (HM μ).N,
            (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) * vt HM μ u k
              + rt (fc := fc) HM μ u k) ^ 2 :=
      Finset.sum_congr rfl (fun k _ => by simp only [hbf k])
    rw [heq]
    exact finset_sum_sq_add_le Finset.univ
      (fun k : Lab (HM μ).N => fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ)
        * vt HM μ u k)
      (fun k : Lab (HM μ).N => rt (fc := fc) HM μ u k)
  -- (F) the `root1` combination
  have hLD : Real.sqrt (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101) * κ
      ≤ Real.sqrt (27 * tailE) := devRoot_mul_le hκ1 hκ hrad2
  have hLD' : Real.sqrt (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101)
      ≤ Real.sqrt (27 * tailE) / κ := by
    rw [le_div_iff₀ hκ]
    exact hLD
  have hTap : Real.sqrt (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101)
        * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)
      ≤ (Real.sqrt (27 * tailE) / κ) * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) :=
    mul_le_mul_of_nonneg_right hLD' (Real.sqrt_nonneg _)
  have hVroot : Real.sqrt (∑ k ∈ S, (vt HM μ u k) ^ 2)
      ≤ Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
        + Real.sqrt (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101)
          * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) := by
    have h := Real.sqrt_le_sqrt hVtS2
    rw [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))] at h
    exact h
  have hP : Real.sqrt (∑ k : Lab (HM μ).N,
        (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) * vt HM μ u k) ^ 2)
      ≤ Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
        + (Real.sqrt (27 * tailE) / κ) * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) := by
    calc Real.sqrt (∑ k : Lab (HM μ).N,
          (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) * vt HM μ u k) ^ 2)
        ≤ Real.sqrt (∑ k ∈ S, (vt HM μ u k) ^ 2) := Real.sqrt_le_sqrt hVtS
      _ ≤ Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
            + Real.sqrt (tailE * (2 * κ / Real.pi + 1) ^ 3 / rad (HM μ).N (2 * κ) ^ 101)
              * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) := hVroot
      _ ≤ Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
            + (Real.sqrt (27 * tailE) / κ) * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) :=
          add_le_add le_rfl hTap
  have hroot1 : Real.sqrt (∑ k : Lab (HM μ).N,
        (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) * vt HM μ u k) ^ 2)
      + Real.sqrt (∑ k : Lab (HM μ).N, (rt (fc := fc) HM μ u k) ^ 2)
      ≤ Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
        + (Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ)
          * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) := by
    calc Real.sqrt (∑ k : Lab (HM μ).N,
          (fc.f (‖Work.BoseB4.vec (labVec (HM μ).N k)‖ / κ) * vt HM μ u k) ^ 2)
        + Real.sqrt (∑ k : Lab (HM μ).N, (rt (fc := fc) HM μ u k) ^ 2)
        ≤ (Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
            + (Real.sqrt (27 * tailE) / κ) * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2))
          + lipC fc * chiS1 / κ * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) :=
          add_le_add hP hRt
      _ = Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
            + (Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ)
              * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) := by ring
  have hstep2 : (∑ k : Lab (HM μ).N,
        (bfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k) ^ 2)
      ≤ (Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
          + (Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ)
            * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2 :=
    le_trans hbsum
      (pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hroot1 2)
  -- (G) the `Tail` quadratic form
  have hcard : (Fintype.card (Lab (HM μ).N) : ℝ) = ((2 * (HM μ).N + 1) ^ 3 : ℝ) := by
    rw [card_lab]
    push_cast
    ring
  have hcd : ((Fintype.card (Lab (HM μ).N) : ℝ)) / rad (HM μ).N (2 * κ) ^ 101
      ≤ 27 / (Real.pi ^ 101 * κ ^ 2) := by
    rw [hcard]
    exact card_div_rad_le (HM μ).N κ hN2n hκ1 h2κ
  have hsq : tailQ * (Fintype.card (Lab (HM μ).N) : ℝ) / rad (HM μ).N (2 * κ) ^ 101
      ≤ (Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ) ^ 2 := by
    calc tailQ * (Fintype.card (Lab (HM μ).N) : ℝ) / rad (HM μ).N (2 * κ) ^ 101
        = tailQ * (((Fintype.card (Lab (HM μ).N) : ℝ)) / rad (HM μ).N (2 * κ) ^ 101) := by ring
      _ ≤ tailQ * (27 / (Real.pi ^ 101 * κ ^ 2)) := mul_le_mul_of_nonneg_left hcd htQ
      _ = (Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ) ^ 2 := by
            rw [div_pow, Real.sq_sqrt
              (div_nonneg (mul_nonneg (by norm_num) htQ) (pow_nonneg Real.pi_pos.le 101))]
            ring
  have htail2 : (∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
        wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i
          * wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u j
          * Tail (HM μ).N i j)
      ≤ (Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ) ^ 2
        * (∑ l : Fin (HM μ).m, (u l) ^ 2) :=
    le_trans htail (mul_le_mul_of_nonneg_right hsq hUnn)
  -- (H) the row constant
  have hrow0 : (Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ)
        + Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ ≤ rowC fc / κ := by
    have hD0 : 0 ≤ 27 * tailE := mul_nonneg (by norm_num) htE
    have hE0 : 0 ≤ 27 * tailQ / Real.pi ^ 101 :=
      div_nonneg (mul_nonneg (by norm_num) htQ) (pow_nonneg Real.pi_pos.le 101)
    have h1 : Real.sqrt (27 * tailE) + lipC fc * chiS1
        + Real.sqrt (27 * tailQ / Real.pi ^ 101) ≤ rowC fc := by
      rw [tailE_sum]
      have h2 : Real.sqrt (27 * tailE) ≤ 27 * tailE + 1 := sqrt_le_add_one hD0
      have h3 : Real.sqrt (27 * tailQ / Real.pi ^ 101) ≤ 27 * tailQ / Real.pi ^ 101 + 1 :=
        sqrt_le_add_one hE0
      linarith [h2, h3, hKCnn, hD0, hE0]
    have h5 : Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ
        + Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ
        = (Real.sqrt (27 * tailE) + lipC fc * chiS1
            + Real.sqrt (27 * tailQ / Real.pi ^ 101)) / κ := by ring
    rw [h5, div_le_div_iff₀ hκ hκ]
    exact mul_le_mul_of_nonneg_right h1 (le_of_lt hκ)
  -- (I) the assembly
  have hX0 : 0 ≤ Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
      + (Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ)
        * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) :=
    add_nonneg (Real.sqrt_nonneg _)
      (mul_nonneg (add_nonneg (div_nonneg (Real.sqrt_nonneg _) (le_of_lt hκ))
        (div_nonneg hKCnn (le_of_lt hκ))) (Real.sqrt_nonneg _))
  have hY0 : 0 ≤ Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ
      * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) :=
    mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (le_of_lt hκ)) (Real.sqrt_nonneg _)
  have hRY : (Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ
        * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2
      = (Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ) ^ 2
        * (∑ l : Fin (HM μ).m, (u l) ^ 2) := by
    simp only [mul_pow, Real.sq_sqrt hUnn]
  have hY : (∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
        wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i
          * wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u j
          * Tail (HM μ).N i j)
      ≤ (Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ
          * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2 := by
    rw [hRY]
    exact htail2
  have hXYle : Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
        + (Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ)
          * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)
        + (Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ
          * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2))
      ≤ Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
        + (rowC fc / κ) * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) := by
    have hval : Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
          + (Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ)
            * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)
          + (Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ
            * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2))
        = Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
          + (Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ
              + Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ)
            * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) := by ring
    rw [hval]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hrow0 (Real.sqrt_nonneg _))
  have hfin : (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
        u l * GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l' * u l')
      ≤ (Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
          + (rowC fc / κ) * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2 := by
    rw [hsplit]
    have hsqXY : (Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
          + (Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ)
            * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2
        + (Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ
            * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2
        ≤ (Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
          + (Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ)
            * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)
          + (Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ
            * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2))) ^ 2 := by
      nlinarith [mul_nonneg hX0 hY0]
    calc (∑ k : Lab (HM μ).N,
            (bfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k) ^ 2)
          + (∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
            wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i
              * wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u j
              * Tail (HM μ).N i j)
        ≤ (Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
            + (Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ)
              * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2
          + (Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ
              * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2 := add_le_add hstep2 hY
      _ ≤ (Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
            + (Real.sqrt (27 * tailE) / κ + lipC fc * chiS1 / κ)
              * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)
            + (Real.sqrt (27 * tailQ / Real.pi ^ 101) / κ
              * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2))) ^ 2 := hsqXY
      _ ≤ (Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
            + (rowC fc / κ) * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (add_nonneg hX0 hY0) hXYle 2
  have hUroot : Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2) ^ 2
      = ∑ l : Fin (HM μ).m, (u l) ^ 2 := Real.sq_sqrt hUnn
  calc (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
        u l * GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l' * u l')
      ≤ (Real.sqrt (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
          + (rowC fc / κ) * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2 := hfin
    _ ≤ (1 + ε) * (∑ k : Lab (HM μ).N, (gram ((HM μ).f k) u) ^ 2)
          + (1 + 1 / ε) * ((rowC fc / κ) * Real.sqrt (∑ l : Fin (HM μ).m, (u l) ^ 2)) ^ 2 :=
        young_sqrt hFFnn (mul_nonneg (div_nonneg (rowC_nonneg fc) (le_of_lt hκ)) hrootU) hε
    _ = (1 + ε) * (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
            u l * GchiF HM μ l l' * u l')
          + (1 + 1 / ε) * (rowC fc / honCutRad v μ) ^ 2 * ∑ l : Fin (HM μ).m, (u l) ^ 2 := by
        rw [hFFeq, mul_pow, hUroot, hκdef]
        ring

/-! ## 10. The Fock lift -/

/-- Additivity of the quadratic form of a matrix difference. -/
lemma quad_add_sub {m : ℕ} (B C A : Fin m → Fin m → ℝ) (u : Fin m → ℝ) :
    (∑ i : Fin m, ∑ j : Fin m, u i * (B i j + C i j - A i j) * u j)
      = (∑ i : Fin m, ∑ j : Fin m, u i * B i j * u j)
        + (∑ i : Fin m, ∑ j : Fin m, u i * C i j * u j)
        - (∑ i : Fin m, ∑ j : Fin m, u i * A i j * u j) := by
  have h1 : ∀ i : Fin m, (∑ j : Fin m, u i * (B i j + C i j - A i j) * u j)
      = (∑ j : Fin m, u i * B i j * u j) + (∑ j : Fin m, u i * C i j * u j)
        - (∑ j : Fin m, u i * A i j * u j) := by
    intro i
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib, Finset.sum_add_distrib]

/-- Factoring a scalar out of the quadratic form of a matrix. -/
lemma quad_smul_left {m : ℕ} (c : ℝ) (M : Fin m → Fin m → ℝ) (u : Fin m → ℝ) :
    (∑ i : Fin m, ∑ j : Fin m, u i * (c * M i j) * u j)
      = c * (∑ i : Fin m, ∑ j : Fin m, u i * M i j * u j) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The quadratic form of the diagonal matrix `γ·1`. -/
lemma quad_diag_smul {m : ℕ} (γ : ℝ) (u : Fin m → ℝ) :
    (∑ i : Fin m, ∑ j : Fin m, u i * (γ * (if i = j then (1 : ℝ) else 0)) * u j)
      = γ * ∑ i : Fin m, (u i) ^ 2 := by
  rw [show (∑ i : Fin m, ∑ j : Fin m, u i * (γ * (if i = j then (1 : ℝ) else 0)) * u j)
      = γ * (∑ i : Fin m, ∑ j : Fin m, u i * (if i = j then (1 : ℝ) else 0) * u j) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring]
  rw [gchi_quad_diag]

theorem gchiAtN_of_matLe (C₁ κ ε : ℝ) (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ) (hε : 0 < ε)
    (hmat : ∀ u : Fin (HM μ).m → ℝ,
      (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
          u l * GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ l l' * u l')
        ≤ (1 + ε) * (∑ l : Fin (HM μ).m, ∑ l' : Fin (HM μ).m,
            u l * GchiF HM μ l l' * u l')
          + ((1 + 1 / ε) * (C₁ / κ) ^ 2) * ∑ l : Fin (HM μ).m, (u l) ^ 2) :
    GchiAtN (v := v) (h := h) (fc := fc) (fu := fu) C₁ κ HM μ ε := by
  set γ : ℝ := (1 + 1 / ε) * (C₁ / κ) ^ 2 with hγ
  intro Ψ
  have hsym : ∀ i j : Fin (HM μ).m,
      ((1 + ε) * GchiF HM μ i j + γ * (if i = j then (1 : ℝ) else 0))
        - GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ i j
      = ((1 + ε) * GchiF HM μ j i + γ * (if j = i then (1 : ℝ) else 0))
        - GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ j i := by
    intro i j
    rw [GchiF_symm HM μ i j, GchiA_symm HM μ i j]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij)]
  have hquad : ∀ u : Fin (HM μ).m → ℝ,
      0 ≤ ∑ i : Fin (HM μ).m, ∑ j : Fin (HM μ).m,
          u i * (((1 + ε) * GchiF HM μ i j + γ * (if i = j then (1 : ℝ) else 0))
            - GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ i j) * u j := by
    intro u
    rw [quad_add_sub, quad_smul_left, quad_diag_smul]
    have hγ' : γ = (1 + 1 / ε) * (C₁ / κ) ^ 2 := hγ
    linarith [hmat u]
  have key := besselOpMat_le_of_mat (m := (HM μ).m)
    (A := GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ)
    (B := fun l l' : Fin (HM μ).m => (1 + ε) * GchiF HM μ l l')
    (C := fun l l' : Fin (HM μ).m => γ * (if l = l' then (1 : ℝ) else 0))
    (by
      intro i j
      exact hsym i j) (by
      intro u
      exact hquad u) Ψ
  have hB : besselOpMat (HM μ).m (fun l l' : Fin (HM μ).m => (1 + ε) * GchiF HM μ l l')
      = (1 + ε) • (honF v h fc fu HM μ).allNumOp := by
    rw [show (fun l l' : Fin (HM μ).m => (1 + ε) * GchiF HM μ l l') = (1 + ε) • GchiF HM μ from by
      funext l l'
      simp only [Pi.smul_apply, smul_eq_mul]]
    rw [besselOpMat_smul, besselOpMat_GchiF (v := v) (h := h) (fc := fc) (fu := fu) HM μ]
    rfl
  have hC : besselOpMat (HM μ).m
        (fun l l' : Fin (HM μ).m => γ * (if l = l' then (1 : ℝ) else 0))
      = γ • (honT v h fc fu HM μ).N := by
    rw [show (fun l l' : Fin (HM μ).m => γ * (if l = l' then (1 : ℝ) else 0))
        = γ • (fun l l' : Fin (HM μ).m => if l = l' then (1 : ℝ) else 0) from by
      funext l l'
      simp only [Pi.smul_apply, smul_eq_mul]]
    rw [besselOpMat_smul, besselOpMat_diag_eq_totNumOp]
    rfl
  rw [hB, hC, besselOpMat_GchiA (v := v) (h := h) (fc := fc) (fu := fu) HM μ] at key
  have key2 : (honF v h fc fu HM μ).qw Ψ ((honT v h fc fu HM μ).Gop (honE v h fc fu HM μ))
      ≤ (honF v h fc fu HM μ).qw Ψ ((1 + ε) • (honF v h fc fu HM μ).allNumOp)
        + (honF v h fc fu HM μ).qw Ψ (γ • (honT v h fc fu HM μ).N) := key
  rw [Work.BoseB7.FockData.qw_smul, Work.BoseB7.FockData.qw_smul] at key2
  have hgoal : (honF v h fc fu HM μ).qw Ψ ((honT v h fc fu HM μ).Gop (honE v h fc fu HM μ))
      ≤ (1 + ε) * (honF v h fc fu HM μ).qw Ψ (honF v h fc fu HM μ).allNumOp
        + (1 + 1 / ε) * (C₁ / κ) ^ 2 * (honF v h fc fu HM μ).qw Ψ (honT v h fc fu HM μ).N := by
    rw [hγ] at key2
    linarith [key2]
  exact hgoal

end RowGchiNAux

end Work.BoseRowQ2
