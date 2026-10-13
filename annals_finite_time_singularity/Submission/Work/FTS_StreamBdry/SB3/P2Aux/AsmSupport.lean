import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB1.Engine
import Submission.Work.FTS_StreamBdry.SB1.psiP_ode
import Submission.Work.FTS_StreamBdry.SB1.psiP_diff
import Submission.Work.FTS_StreamBdry.SB1.psiP_Vop_bnd
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB3.psiP_D3_le
import Submission.Work.FTS_StreamBdry.SB3.law_psiP
import Submission.Work.FTS_StreamBdry.SB25.gaugeMode_facts
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB3.P2Aux.AsmSupport` — support lemmas for `pthIter2_le`

Generic helpers used by the assembly of `SB3.pthIter2_le`:

* `psiP_c3` — `psiP αG Ψ` is `C³` on the open quadrant (the `C²` proof `SB3.psiP_c2`,
  with the SB1′ decomposition `Ψ = psiP + κ·gaugeMode` and the analyticity of the gauge mode);
* `bslOp_psiP` — the elliptic law for the `U`-slot part, `bslOp αG (psiP αG Ψ) = F` on `Qd`
  (same proof as `SB3.law_psiP`, stopping one step earlier);
* `Dz_div`, `DzIter_div_eqOn`, `DzIter_congr_isOpen`, `DzIter_Dz_eqOn`, `pz_smooth_of`,
  `Dz_smooth_of`, `div_identities` — the calculus of `D_z^j (Q / s2)` needed to pass the
  bounds on `D_z^j (psiP)` to the functions `u = psiP/s2`, `u₁ = D_zpsiP/s2`;
* `abs_div_s2_le_of`, `abs_s2_mul_le_of`, `abs_two_sin_sq_mul_le_of`, `abs_comb_le_of`,
  `abs_neg_sub_le_of` — pointwise `abs` bookkeeping.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB3.P2Aux

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP gaugeMode)

set_option autoImplicit false

lemma isOpen_Qd_asm : IsOpen Work.Construction.Qd := isOpen_Ioi.prod isOpen_Ioo

/-- `psiP αG Ψ` is `C^3` on the open quadrant. -/
theorem psiP_c3 {αG M : ℝ} (hαG : 0 < αG) {Ψ : ℝ → ℝ → ℝ}
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ContDiffOn ℝ 3 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd := by
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M)
    hαG h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
  have hg : ContDiffOn ℝ 3
      (Function.uncurry (gaugeMode αG)) Work.Construction.Qd :=
    (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode αG).of_le le_top
  have hsub : ContDiffOn ℝ 3
      (fun p : ℝ × ℝ =>
        Function.uncurry Ψ p - κ * Function.uncurry (gaugeMode αG) p)
      Work.Construction.Qd :=
    h3.sub (contDiffOn_const.mul hg)
  refine hsub.congr (fun p hp => ?_)
  obtain ⟨z, θ⟩ := p
  have h := hκ z θ hp
  simp only [Function.uncurry]
  linarith

/-- `bslOp αG (psiP αG Ψ) = F` on the open quadrant. -/
theorem bslOp_psiP {αG M : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : SlotBd αG Ψ M) :
    ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      Work.Elliptic.bslOp αG (psiP αG Ψ) z θ = F z θ := by
  obtain ⟨κ, hκ⟩ := Work.FTS_StreamBdry.SB1.sb1_gauge_of_parts (αG := αG) (M := M)
    hαG h3 hslot
    (Work.FTS_StreamBdry.SB1.psiP_ode hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_diff hαG h3 hslot)
    (Work.FTS_StreamBdry.SB1.psiP_Vop_bnd hαG h3 hslot)
  have hC2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot
  have hgau : ContDiffOn ℝ 2 (Function.uncurry (gaugeMode αG)) Work.Construction.Qd :=
    (Work.FTS_StreamBdry.SB25.contDiffOn_uncurry_gaugeMode αG).of_le le_top
  intro z θ hmem
  obtain ⟨hz, hθ1, hθ2⟩ := Work.FTS_StreamBdry.mem_Qd.mp hmem
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (Work.FTS_StreamBdry.cos_pos_of_Qd hmem)
  have hnbhd : Work.Construction.Qd ∈ 𝓝 (z, θ) :=
    Work.FTS_StreamBdry.SB25.qd_isOpen.mem_nhds ⟨hz, hθ1, hθ2⟩
  have hev : ∀ᶠ q in 𝓝 (z, θ),
      Ψ q.1 q.2 = (psiP αG Ψ q.1 q.2 + κ * gaugeMode αG q.1 q.2) :=
    Filter.mem_of_superset hnbhd (fun q hq => hκ q.1 q.2 hq)
  have hcongr : Work.Elliptic.bslOp αG Ψ z θ
      = Work.Elliptic.bslOp αG (fun z θ =>
          psiP αG Ψ z θ + κ * gaugeMode αG z θ) z θ :=
    Work.FTS.H2.PhiStarE5.bslOp_congr_of_eventuallyEq αG hev
  have hg2 : ContDiffAt ℝ 2
      (Function.uncurry (fun z θ => κ * gaugeMode αG z θ)) (z, θ) :=
    (hgau.contDiffAt hnbhd).const_smul κ
  have hadd : Work.Elliptic.bslOp αG (fun z θ =>
        psiP αG Ψ z θ + κ * gaugeMode αG z θ) z θ
      = Work.Elliptic.bslOp αG (psiP αG Ψ) z θ
        + Work.Elliptic.bslOp αG (fun z θ => κ * gaugeMode αG z θ) z θ :=
    Work.Elliptic.bslOp_add αG (psiP αG Ψ)
      (fun z θ => κ * gaugeMode αG z θ) z θ hcos
      (hC2.contDiffAt hnbhd) hg2
  have hD0 : Work.Elliptic.bslOp αG (fun z θ => κ * gaugeMode αG z θ) z θ = 0 := by
    rw [Work.FTS.BSIdent.OddExt.bslOp_const_mul αG κ (gaugeMode αG) z θ,
      ((Work.FTS_StreamBdry.SB25.gaugeMode_facts hαG).2 z θ hmem).2, mul_zero]
  calc Work.Elliptic.bslOp αG (psiP αG Ψ) z θ
      = Work.Elliptic.bslOp αG (fun z θ =>
          psiP αG Ψ z θ + κ * gaugeMode αG z θ) z θ := by
        rw [hadd, hD0, add_zero]
    _ = Work.Elliptic.bslOp αG Ψ z θ := hcongr.symm
    _ = F z θ := hsol.1 z hz θ hθ1 hθ2

/-! ## §2 `D_z` of a division by a `θ`-only function, and its iterates -/

/-- `D_z` of a division by a `θ`-only function. -/
lemma Dz_div {c : ℝ → ℝ} {Q : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hd : DifferentiableAt ℝ (fun z' => Q z' θ) z) :
    Work.Spaces.Dz (fun z θ' => Q z θ' / c θ') z θ = Work.Spaces.Dz Q z θ / c θ := by
  show z * deriv (fun z' => Q z' θ / c θ) z = z * deriv (fun z' => Q z' θ) z / c θ
  rw [show (fun z' => Q z' θ / c θ) = fun z' => (c θ)⁻¹ * Q z' θ from by
    funext z'; rw [div_eq_inv_mul]]
  rw [deriv_const_mul _ hd]
  ring

/-- Congruence of `D_z^j` on an open set. -/
lemma DzIter_congr_isOpen {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j f))
      (Function.uncurry (Work.Spaces.DzIter j g)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
      intro p hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j f) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j g) p.1 p.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

/-- `D_z^j (D_z Q) = D_z^{j+1} Q` on an open set. -/
lemma DzIter_Dz_eqOn {Q : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (Work.Spaces.Dz Q)))
      (Function.uncurry (Work.Spaces.DzIter (j + 1) Q)) V := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      intro p hp
      have hc : Work.Spaces.Dz (Work.Spaces.DzIter j (Work.Spaces.Dz Q)) p.1 p.2
          = Work.Spaces.Dz (Work.Spaces.DzIter (j + 1) Q) p.1 p.2 := by
        show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Spaces.Dz Q)) p.1 p.2
          = p.1 * Work.Spaces.pz (Work.Spaces.DzIter (j + 1) Q) p.1 p.2
        rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]
      exact hc

/-- The division identity for `D_z^j` on an open set. -/
lemma DzIter_div_eqOn {c : ℝ → ℝ} {Q : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    {j : ℕ}
    (hd : ∀ i, i < j → ∀ p ∈ V,
      DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter i Q z' p.2) p.1) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (fun z θ => Q z θ / c θ)))
      (Function.uncurry (fun z θ => Work.Spaces.DzIter j Q z θ / c θ)) V := by
  induction j with
  | zero => intro p hp; rfl
  | succ j ih =>
      intro p hp
      have ihj : Set.EqOn (Function.uncurry (Work.Spaces.DzIter j (fun z θ => Q z θ / c θ)))
          (Function.uncurry (fun z θ => Work.Spaces.DzIter j Q z θ / c θ)) V :=
        ih (fun i hi => hd i (Nat.lt_succ_of_lt hi))
      have hcongr : Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => Q z θ / c θ)) p.1 p.2
          = Work.Spaces.Dz (fun z θ => Work.Spaces.DzIter j Q z θ / c θ) p.1 p.2 := by
        show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j (fun z θ => Q z θ / c θ)) p.1 p.2
          = p.1 * Work.Spaces.pz (fun z θ => Work.Spaces.DzIter j Q z θ / c θ) p.1 p.2
        rw [Work.Spaces.pz_congr_of_isOpen hV ihj hp]
      show Work.Spaces.Dz (Work.Spaces.DzIter j (fun z θ => Q z θ / c θ)) p.1 p.2
        = Work.Spaces.Dz (Work.Spaces.DzIter j Q) p.1 p.2 / c p.2
      rw [hcongr, Dz_div (hd j (Nat.lt_succ_self j) p hp)]

/-- `∂_z` costs one order of smoothness (at finite order) on an open set. -/
lemma pz_smooth_of {Q : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry Q) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz Q)) V :=
  Work.FTS_StreamBdry.SB3.psiP_D3_aux_pz_smooth hV h

/-- `D_z` maps `C^{n+1}` functions to `C^n` functions on an open set. -/
lemma Dz_smooth_of {Q : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry Q) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz Q)) V := by
  have hpz : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz Q)) V := pz_smooth_of hV h
  have hmul : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz Q) p) V :=
    contDiff_fst.contDiffOn.mul hpz
  refine hmul.congr (fun p hp => ?_)
  rfl

/-- **The division identities.**  If `P` is `C^3` on `Qd`, then for `u = P/s2` and
`u₁ = (D_zP)/s2`: `D_z^j u = (D_z^j P)/s2` for `j ≤ 3` and `D_z^j u₁ = (D_z^{j+1} P)/s2` for
`j ≤ 2`, on `Qd`. -/
lemma div_identities {P : ℝ → ℝ → ℝ}
    (hPc3 : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd) :
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 3,
        Work.Spaces.DzIter j (fun z θ => P z θ / Work.Construction.s2 θ) z θ
          = Work.Spaces.DzIter j P z θ / Work.Construction.s2 θ) ∧
    (∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
        Work.Spaces.DzIter j (fun z θ => Work.Spaces.Dz P z θ / Work.Construction.s2 θ) z θ
          = Work.Spaces.DzIter (j + 1) P z θ / Work.Construction.s2 θ) := by
  have hV : IsOpen Work.Construction.Qd := isOpen_Qd_asm
  have h0 : ContDiffOn ℝ 3 (Function.uncurry P) Work.Construction.Qd := hPc3
  have h1 : ContDiffOn ℝ 2 (Function.uncurry (Work.Spaces.DzIter 1 P))
      Work.Construction.Qd := Dz_smooth_of hV h0
  have h2 : ContDiffOn ℝ 1 (Function.uncurry (Work.Spaces.DzIter 2 P))
      Work.Construction.Qd := Dz_smooth_of hV h1
  have hdiff : ∀ i ≤ 2, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter i P z' θ) z := by
    intro i hi z θ hmem
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
    · exact Work.Spaces.differentiableAt_curry_left
        ((h0.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hmem))
    · exact Work.Spaces.differentiableAt_curry_left
        ((h1.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hmem))
    · exact Work.Spaces.differentiableAt_curry_left
        ((h2.differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds hmem))
  refine ⟨?_, ?_⟩
  · intro z θ h j hj
    have h1' := DzIter_div_eqOn (c := Work.Construction.s2) hV
      (j := j) (fun i hi p hp => hdiff i (by omega) p.1 p.2 hp) h
    simpa only [Function.uncurry] using h1'
  · intro z θ h j hj
    have heq : Set.EqOn
        (Function.uncurry (fun z θ => Work.Spaces.Dz P z θ / Work.Construction.s2 θ))
        (Function.uncurry (Work.Spaces.Dz (fun z θ => P z θ / Work.Construction.s2 θ)))
        Work.Construction.Qd := by
      intro p hp
      exact (Dz_div (c := Work.Construction.s2) (Q := P)
        (hd := hdiff 0 (by norm_num) p.1 p.2 hp)).symm
    have hc := DzIter_congr_isOpen hV heq j h
    have h3 : Work.Spaces.DzIter (j + 1)
        (fun z θ => P z θ / Work.Construction.s2 θ) z θ
        = Work.Spaces.DzIter (j + 1) P z θ / Work.Construction.s2 θ :=
      DzIter_div_eqOn (c := Work.Construction.s2) hV
        (j := j + 1) (fun i hi p hp => hdiff i (by omega) p.1 p.2 hp) h
    have hmid : Work.Spaces.DzIter j
        (Work.Spaces.Dz (fun z θ => P z θ / Work.Construction.s2 θ)) z θ
        = Work.Spaces.DzIter (j + 1) (fun z θ => P z θ / Work.Construction.s2 θ) z θ := by
      simpa only [Function.uncurry] using
        DzIter_Dz_eqOn (Q := fun z θ => P z θ / Work.Construction.s2 θ) hV j h
    have hc' : Work.Spaces.DzIter j
        (fun z θ => Work.Spaces.Dz P z θ / Work.Construction.s2 θ) z θ
        = Work.Spaces.DzIter j
            (Work.Spaces.Dz (fun z θ => P z θ / Work.Construction.s2 θ)) z θ := by
      simpa only [Function.uncurry] using hc
    calc Work.Spaces.DzIter j (fun z θ => Work.Spaces.Dz P z θ / Work.Construction.s2 θ) z θ
        = Work.Spaces.DzIter j
            (Work.Spaces.Dz (fun z θ => P z θ / Work.Construction.s2 θ)) z θ := hc'
      _ = Work.Spaces.DzIter (j + 1)
            (fun z θ => P z θ / Work.Construction.s2 θ) z θ := hmid
      _ = Work.Spaces.DzIter (j + 1) P z θ / Work.Construction.s2 θ := h3

/-! ## §3 Pointwise `abs` bookkeeping -/

/-- `|X / s2 θ| ≤ K` from `|X| ≤ K * s2 θ`. -/
lemma abs_div_s2_le_of {X K θ : ℝ} (hsp : 0 < Work.Construction.s2 θ)
    (h : |X| ≤ K * Work.Construction.s2 θ) : |X / Work.Construction.s2 θ| ≤ K := by
  rw [abs_div, abs_of_pos hsp, div_le_iff₀ hsp]
  exact h

/-- `|s2 θ * X| ≤ K` from `|X| ≤ K` and `s2 θ ≤ 1`. -/
lemma abs_s2_mul_le_of {X K θ : ℝ} (hsp : 0 ≤ Work.Construction.s2 θ)
    (hs2 : Work.Construction.s2 θ ≤ 1) (hK : 0 ≤ K) (h : |X| ≤ K) :
    |Work.Construction.s2 θ * X| ≤ K := by
  rw [abs_mul, abs_of_nonneg hsp]
  calc Work.Construction.s2 θ * |X| ≤ 1 * K :=
        mul_le_mul hs2 h (abs_nonneg _) (by norm_num)
    _ = K := one_mul K

/-- `|2 sin²θ * X| ≤ 2K` from `|X| ≤ K`, `K ≥ 0`. -/
lemma abs_two_sin_sq_mul_le_of {X K θ : ℝ} (_hK : 0 ≤ K) (h : |X| ≤ K) :
    |2 * Real.sin θ ^ 2 * X| ≤ 2 * K := by
  have hsin : Real.sin θ ^ 2 ≤ 1 := by
    nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ, sq_nonneg (Real.sin θ)]
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.sin θ ^ 2)]
  nlinarith

/-- `|α²X + 5αY| ≤ α²MX + 5αMY` from `|X| ≤ MX`, `|Y| ≤ MY`. -/
lemma abs_comb_le_of {X Y α MX MY : ℝ} (hα : 0 < α) (hX : |X| ≤ MX) (hY : |Y| ≤ MY) :
    |α ^ 2 * X + 5 * α * Y| ≤ α ^ 2 * MX + 5 * α * MY := by
  refine (abs_add_le _ _).trans ?_
  have ha : |α ^ 2 * X| ≤ α ^ 2 * MX := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ α ^ 2)]
    exact mul_le_mul_of_nonneg_left hX (by positivity)
  have hb : |5 * α * Y| ≤ 5 * α * MY := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 5 * α)]
    exact mul_le_mul_of_nonneg_left hY (by positivity)
  linarith

/-- `|-A - B| ≤ CA + CB` from `|A| ≤ CA`, `|B| ≤ CB`. -/
lemma abs_neg_sub_le_of {A B CA CB : ℝ} (hA : |A| ≤ CA) (hB : |B| ≤ CB) :
    |-(A) - B| ≤ CA + CB := by
  refine (abs_sub _ _).trans ?_
  rw [abs_neg]
  linarith

/-- `|-4 * s2 θ * X| ≤ 4K` from `|X| ≤ K` and `s2 θ ≤ 1`. -/
lemma abs_four_s2_mul_le_of {X K θ : ℝ} (hsp : 0 ≤ Work.Construction.s2 θ)
    (hs2 : Work.Construction.s2 θ ≤ 1) (hK : 0 ≤ K) (h : |X| ≤ K) :
    |-4 * Work.Construction.s2 θ * X| ≤ 4 * K := by
  have h1 : |Work.Construction.s2 θ * X| ≤ K := abs_s2_mul_le_of hsp hs2 hK h
  have h2 : -4 * Work.Construction.s2 θ * X
      = -(4 * (Work.Construction.s2 θ * X)) := by ring
  rw [h2, abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
  linarith

/-- `|A + B - C - D| ≤ a + b + c + d` from the four `abs` bounds. -/
lemma abs_four_le_of {A B C D a b c d : ℝ} (hA : |A| ≤ a) (hB : |B| ≤ b)
    (hC : |C| ≤ c) (hD : |D| ≤ d) : |A + B - C - D| ≤ a + b + c + d := by
  have h1 : |A + B - C - D| ≤ |A| + |B| + |C| + |D| := by
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith [neg_abs_le A, neg_abs_le B, le_abs_self C, le_abs_self D]
    · linarith [le_abs_self A, le_abs_self B, neg_abs_le C, neg_abs_le D]
  linarith

/-- Differentiability of `θ ↦ Q z θ / s2 θ`. -/
lemma differentiableAt_div_s2 {Q : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hQ : DifferentiableAt ℝ (fun θ' => Q z θ') θ)
    (hs2 : Work.Construction.s2 θ ≠ 0) :
    DifferentiableAt ℝ (fun θ' => Q z θ' / Work.Construction.s2 θ') θ := by
  have hds : DifferentiableAt ℝ (fun θ' : ℝ => Work.Construction.s2 θ') θ := by
    show DifferentiableAt ℝ (fun θ' : ℝ => Real.sin (2 * θ')) θ
    fun_prop
  exact hQ.div hds hs2

end Work.FTS_StreamBdry.SB3.P2Aux
