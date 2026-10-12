import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.BoseK15.Constants
import Submission.Work.BoseK15.Guarded
import Submission.Work.BoseK15.ell_mul_KL_sqrt
import Submission.Work.BoseK15.lattice_rows
import Submission.Work.BoseK15.sum_wt_abs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseK15.BoxInhabited` — the bundle is inhabited at the box

`Work.BoseK15.Q3Kernel_corpus` and `Work.BoseK15.IntKernel_corpus` consume the
primitive bundle `Work.BoseK15.K15Input K₀ F T E`.  This module *inhabits* that
bundle at the honest box model of FS §10 — `F = boxFockDataBox ℓ kmom …`,
`T = tildeDataBox …` on the corpus χ, `E = Q3Env.ofSect4 …` at FS's parameter
point — so that those two theorems are not vacuous.

The model is passed as a pair `(F, T)` with the *equalities*
`hF : F = boxFockDataBox …`, `hT : T = tildeDataBox …`; every conclusion is stated
about the opaque `F`, `T`, and every fact about the coordinates is turned into a
fact about `F`/`T` by a single rewriting (`Work.BoseK15.…`).

The honest rows that the module takes as input are exactly the ones that are
**not** chapter-internal, i.e. the potential rows (`Ŵ₁`, `Ŵ₁ω`, `ĝ`), the two
Green's-function rows (`omega_lattice`, `sum_diff`) and the first-quantised
`Q₂^ex` cancellation:

* `hfL*` — FS's cutoff profile `f_L` (`K_L√(μa)`-supported, `1` on the inner
  ball, `0 ≤ f_L ≤ 1`, even);
* `hW1*` — FS's `Ŵ₁` (`eq:W1-g` bound, `(1+‖p‖)^{-2}` decay, gradient bound,
  evenness, `C¹`) with its **absolute** constant `Cw`;
* `hW1om0`, `hW1om`, `hCg`, `homega`, `hsumdiff` — FS's `Ŵ₁ω(0)`, `Ŵ₁ω`, `ĝ` and
  the two rows of `lem:EstimateIntegral`;
* `hq2` — the first-quantised `Q₂^ex` cancellation (`eq:Q3Cancels`);
* `halpha`, `hint` — K3 and K5.  Both are *reducible* to the other rows:
  `Work.BoseK15.alpha_lip_of_prims` derives `halpha` from `tau_eq`, `W1_grad_le`,
  the two `P_H^q` positivity rows (`Work.BoseK15.A_ge_AB_of_prims`) and the
  kinetic bound `htaurad` of `Work.BoseK15.arith_tau_ge`; `hint` is
  `Work.BoseB7A.EstIntegralOneA` (`Work.BoseK15.exists_intOne_of_intKernel`),
  whose derivation consumes the bundle's Green's-function rows.  They are taken
  here as inputs so that the inhabitation does not depend on those modules;
* `haddO`, `haddI` — the two *guarded* label additivities (the design's §5
  wrap-around; the unguarded form is refutable, `Work.BoseK15.Obstruction`).

Everything else is chapter-internal: the χ-decay constants (`exists_constants`),
the four lattice rows (`lattice_rows`), the scaled weighted lattice sum
(`sum_wt_abs`), the ball count (`card_le_of_vec_norm_le`), the guarded
`hasKernel` (`hasKernel_guarded`) and `ℓ·K_L√(μa) = K_ℓK_L`
(`ell_mul_KL_sqrt`).

**The chapter constant.** `K₀` is built here as the `max'` of a *finite explicit*
set containing `8` and every auxiliary constant — it is therefore absolute and is
never read off the instance: all the domination fields `K₀_*` of the bundle are
proved from membership in that set.
-/

noncomputable section

open scoped BigOperators Pointwise ContDiff
open MeasureTheory Classical

namespace Work.BoseK15

open Work.BoseB7 Work.BoseB7A

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

universe u

set_option maxHeartbeats 1600000 in
/-- **The bundle is inhabited at the honest box model.**  See the module
docstring for the origin of each hypothesis; `F`/`T` are the box model, with
`hF`/`hT` their defining equalities. -/
theorem exists_K15Input_box {Mode : Type u} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    (ℓ : ℝ) (hℓ : 1 ≤ ℓ) (kmom : Mode → ℝ³)
    (hkmom : ∀ i : Mode, kmom (-i) = -kmom i)
    (hlat : OnDualLattice ℓ kmom)
    (m : ℕ) (f g : Mode → Fin m → ℝ)
    (hf : ∀ i j : Mode, Work.BoseB4.gram (f i) (f j) =
      Work.BoseB7.ccrKernel ℓ corpusBox.hatChiSq corpusBox.hatChi (kmom i) (kmom j))
    (hg : ∀ s t : Mode, s ≠ 0 → t ≠ 0 →
      Work.BoseB4.gram (g s) (g t) = if s = t then 1 else 0)
    (hcross : ∀ s k : Mode, Work.BoseB4.gram (g s) (f k)
      = corpusBox.hatChi (ℓ • (kmom k - kmom s)))
    (F : FockData Mode) (T : TildeData F)
    (hF : F = boxFockDataBox ℓ kmom hkmom m f hf)
    (hccrX : ∀ s k : Mode, T.ccrX s k
      = corpusBox.hatChi (ℓ • (kmom k - kmom s)))
    (z μ a KH Kl KL d s eT b : ℝ) (intM : ℕ) (bigM δ : ℝ)
    (fLf W1f W1omegaf : ℝ³ → ℝ) (W1omega0 : ℝ) (gHat : Mode → ℝ)
    (E : Q3Env Mode)
    (hE : E = Work.BoseB4.Q3Env.ofSect4 kmom z ℓ μ a KH Kl KL d s eT b intM bigM δ
      fLf W1f W1omegaf (Work.BoseB4.tauFun eT s d ℓ) W1omega0 corpusBox)
    (hv : FSParamsView E)
    (haddO : ∀ i j : Mode,
      E.fL i ≠ 0 → j ∈ F.PHset E → kmom (i - j) = kmom i - kmom j)
    (haddI : ∀ i j : Mode, E.fL i ≠ 0 → E.fL j ≠ 0 → kmom (i - j) = kmom i - kmom j)
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hW1le : ∀ p : ℝ³, |W1f p| ≤ Cw * E.aScat)
    (hW1decay : ∀ p : ℝ³, |W1f p| * (1 + ‖p‖) ^ 2 ≤ Cw * E.aScat)
    (hW1grad : ∀ p : ℝ³, ‖fderiv ℝ W1f p‖ ≤ Cw * E.aScat * (1 + ‖p‖))
    (hW1even : ∀ p : ℝ³, W1f (-p) = W1f p)
    (hW1cd : ContDiff ℝ 1 W1f)
    (hW1om : ∀ p : ℝ³, 0 ≤ W1omegaf p)
    (hW1om0 : ∃ C : ℝ, 0 ≤ C ∧ 0 ≤ W1omega0 ∧ W1omega0 ≤ C * E.aScat)
    (hfL0 : ∀ p : ℝ³, 0 ≤ fLf p) (hfL1 : ∀ p : ℝ³, fLf p ≤ 1)
    (hfLe : ∀ p : ℝ³, fLf (-p) = fLf p)
    (hfLsup : ∀ p : ℝ³, fLf p ≠ 0 → ‖p‖ ≤ E.KL * Real.sqrt (E.mu * E.aScat))
    (hfLone : ∀ p : ℝ³, ‖p‖ ≤ E.KL * Real.sqrt (E.mu * E.aScat) → fLf p = 1)
    (hCg : ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Mode, |gHat k| ≤ C * E.aScat)
    (ha1 : E.aScat ≤ 1)
    (homega : ∃ C : ℝ, 0 ≤ C ∧ |W1omega0 - E.ell ^ (-(3 : ℝ)) *
      ∑ k ∈ Work.BoseB7.excited Mode, E.W1 k * gHat k / (2 * ‖kmom k‖ ^ 2)|
        ≤ C * E.aScat ^ 2 / E.ell)
    (hsumdiff : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, E.ell ^ (-(3 : ℝ)) *
      ∑ k ∈ F.PHset E, (gHat k - E.W1 k) ^ 2 / ‖kmom k‖ ^ 2
        ≤ C * E.aScat * (R / E.ell) ^ 4)
    (hq2 : ∀ Ψ : F.H,
      2 * E.rho * W1omega0 * F.qw Ψ (T.Gop E)
        ≤ F.qw Ψ (F.Q2ex E) + (E.b / 400) * F.qw Ψ (T.gapOpT E))
    (halpha : ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : Mode,
      F.PHq E.KH E.aScat p → F.PHq E.KH E.aScat q →
      |E.alpha p - E.alpha q|
        ≤ C * E.lille * (E.KH * E.aScat) * ‖F.kmom p - F.kmom q‖)
    (hint : ∃ C : ℝ, 0 ≤ C ∧ |E.rho * W1omega0 - E.ell ^ (-(3 : ℝ)) *
      ∑ k ∈ F.PHset E, E.W1 k * E.alpha k|
        ≤ C * E.rho * E.aScat * E.KH⁻¹) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ Nonempty (K15Input K₀ F T E) := by
  classical
  -- the definitional identities that read `E` and `F`/`T` off FS's data
  have hAeq : ∀ k : Mode, E.A k = E.tau k + E.rho * E.W1 k :=
    fun k => by rw [hE]; rfl
  have hBeq : ∀ k : Mode, E.B k = E.rho * E.W1 k := fun k => by rw [hE]; rfl
  have hW1eq : ∀ k : Mode, E.W1 k = W1f (kmom k) := fun k => by rw [hE]; rfl
  have hW1omeq : E.W1omega0 = W1omega0 := by rw [hE]; rfl
  have hELL : E.ell = ℓ := by rw [hE]; rfl
  have hkmomeq : ∀ i : Mode, F.kmom i = kmom i := fun i => by rw [hF]; rfl
  have hccrK : ∀ i j : Mode, F.ccrK i j
      = corpusBox.hatChiSq (E.ell • (kmom i - kmom j))
        - corpusBox.hatChi (E.ell • kmom i) * corpusBox.hatChi (E.ell • kmom j) :=
    fun i j => by rw [hF, hELL]; rfl
  have hχεq : ∀ k : Mode, E.hatChi k = corpusBox.hatChi (E.ell • kmom k) :=
    fun k => by rw [hE]; rfl
  have hχ2eq : ∀ k : Mode, E.hatChiSq k = corpusBox.hatChiSq (E.ell • kmom k) :=
    fun k => by rw [hE]; rfl
  have hpow4 : ∀ x : ℝ, 0 ≤ x ^ 4 := by
    intro x
    have h : x ^ 4 = (x ^ 2) * (x ^ 2) := by ring
    rw [h]; exact mul_self_nonneg _
  have hKHpos : 0 < E.KH := lt_of_lt_of_le one_pos hv.one_le_KH
  have hapos : 0 < E.aScat := hv.a_pos
  have hKHa : 0 < E.KH * E.aScat := mul_pos hKHpos hapos
  obtain ⟨Kc, _hKc1, Cchi, Csum, Ctail, Cwt0, hCchi0, hCsum0, hCtail0, hCwt00,
    hdom1, hdom2, hchi, hsumGeom, hsumTail, hsem⟩ := exists_constants
  obtain ⟨Klat, _hKlat0, hlatrows⟩ := lattice_rows
  obtain ⟨CwtAbs, hCwtAbs0, hsumwtAbs⟩ := sum_wt_abs
  obtain ⟨Cw0, hCw00, hW1om0nn, hW1om0le⟩ := hW1om0
  obtain ⟨Cg, hCg0, hgHatle⟩ := hCg
  obtain ⟨Cω, hCω0, homega'⟩ := homega
  obtain ⟨Cd, hCd0, hsumdiff'⟩ := hsumdiff
  obtain ⟨Calpha, hCalpha0, halpha'⟩ := halpha
  obtain ⟨Cint, hCint0, hint'⟩ := hint
  -- the four kinetic-sum rows of `lattice_rows`, instantiated at the box data
  obtain ⟨hlow, hinv4, hinv6, hinv3⟩ :=
    hlatrows ℓ hℓ kmom hlat E.KH E.aScat hv.one_le_KH hv.a_pos
  have hintM : E.intM = 48 := by rw [hv.intM_eq]; rfl
  -- the chapter constant: the `max'` of an explicit finite set
  let Sf : Finset ℝ := {8, Kc, Klat, CwtAbs, Cwt0, Cw0, Cg, Cω, Cd, Calpha, Cint,
    8 * Cw * Cw * max Cwt0 CwtAbs, Cw}
  have hSfne : Sf.Nonempty := ⟨8, by simp [Sf]⟩
  set K₀ : ℝ := Sf.max' hSfne with hK₀def
  have hmem : ∀ x ∈ Sf, x ≤ K₀ := fun x hx => Finset.le_max' Sf x hx
  have h8K : (8 : ℝ) ≤ K₀ := hmem 8 (by simp [Sf])
  have h1K : (1 : ℝ) ≤ K₀ := le_trans (by norm_num) h8K
  have hK₀0 : 0 < K₀ := lt_of_lt_of_le one_pos h1K
  have hKcK : Kc ≤ K₀ := hmem Kc (by simp [Sf])
  have hKlatK : Klat ≤ K₀ := hmem Klat (by simp [Sf])
  have hCw0K : Cw0 ≤ K₀ := hmem Cw0 (by simp [Sf])
  have hCgK : Cg ≤ K₀ := hmem Cg (by simp [Sf])
  have hCωK : Cω ≤ K₀ := hmem Cω (by simp [Sf])
  have hCdK : Cd ≤ K₀ := hmem Cd (by simp [Sf])
  have hCαK : Calpha ≤ K₀ := hmem Calpha (by simp [Sf])
  have hCintK : Cint ≤ K₀ := hmem Cint (by simp [Sf])
  have hCwK : Cw ≤ K₀ := hmem Cw (by simp [Sf])
  have h8wtK : 8 * Cw * Cw * max Cwt0 CwtAbs ≤ K₀ :=
    hmem (8 * Cw * Cw * max Cwt0 CwtAbs) (by simp [Sf])
  -- the two filter descriptions of `F`'s regions
  have hPHfilt : F.PHset E = (Work.BoseB7.excited Mode).filter
      (fun k => 1 / (2 * E.KH * E.aScat) ≤ ‖kmom k‖) := by
    refine Finset.filter_congr ?_
    intro k _
    simp only [FockData.PH, hkmomeq]
  have hPHcom : (Work.BoseB7.excited Mode).filter
      (fun k => ¬ F.PH E.KH E.aScat k)
      = (Work.BoseB7.excited Mode).filter
        (fun k => ¬ (1 / (2 * E.KH * E.aScat) ≤ ‖kmom k‖)) := by
    refine Finset.filter_congr ?_
    intro k _
    simp only [FockData.PH, hkmomeq]
  have hPHqfilt : (Work.BoseB7.excited Mode).filter
      (fun q => F.PHq E.KH E.aScat q)
      = (Work.BoseB7.excited Mode).filter
        (fun q => 1 / (4 * E.KH * E.aScat) ≤ ‖kmom q‖) := by
    refine Finset.filter_congr ?_
    intro q _
    simp only [FockData.PHq, hkmomeq]
  refine ⟨K₀, hK₀0, ⟨?_⟩⟩
  refine
    { ell := E.ell
      ell_eq_E := rfl
      ell_pos := Work.BoseB7.ell_pos E hv
      aScat_pos := hv.a_pos
      Cw := Cw
      Cw_nonneg := hCw
      mu_pos := Work.BoseB7.mu_pos E hv
      KH_pos := hKHpos
      Kl_pos := lt_of_lt_of_le one_pos hv.one_le_Kl
      one_le_KH := hv.one_le_KH
      ell_pos_E := Work.BoseB7.ell_pos E hv
      kmom := kmom
      kmom_eq := hkmomeq
      kmom_neg := hkmom
      kmom_add := haddO
      kmom_add_inner := haddI
      hlat := by rw [hELL]; exact hlat
      ellKL := ell_mul_KL_sqrt E hv
      Cchi := Cchi
      Cchi_nonneg := hCchi0
      chi := hchi
      Csum := Csum
      Csum_nonneg := hCsum0
      sum_geom := hsumGeom
      Ctail := Ctail
      Ctail_nonneg := hCtail0
      sum_geom_tail := by
        intro R Sfins h1 h2
        rw [hintM]
        exact hsumTail R Sfins h1 h2
      Csem := Cwt0
      Csem_nonneg := hCwt00
      sum_sem := by
        rw [hELL]
        exact hsem ℓ hℓ kmom hlat
      Ccard := 1
      one_le_Ccard := le_refl 1
      card_le := by
        intro SC ρ hρ hS
        have h := card_le_of_vec_norm_le SC ρ hρ hS
        have hmono : ρ / Real.pi + 1 ≤ ρ + 1 := by
          have hπ1 : (1 : ℝ) ≤ Real.pi := by
            linarith [Real.one_le_pi_div_two, Real.pi_pos]
          have := div_le_self hρ hπ1
          linarith
        have h2 : (0 : ℝ) ≤ ρ / Real.pi + 1 := by
          have h3 := div_nonneg hρ (le_of_lt Real.pi_pos)
          linarith
        calc (SC.card : ℝ) ≤ (ρ / Real.pi + 1) ^ 3 := h
          _ ≤ (ρ + 1) ^ 3 := pow_le_pow_left₀ h2 hmono 3
          _ = 1 * (ρ + 1) ^ 3 := by ring
      K₀_one := h1K
      K₀_w := hCwK
      K₀_chi := le_trans hdom1 hKcK
      K₀_sum := le_trans hdom2 hKcK
      K₀_card := by simpa using h8K
      Cwt := max Cwt0 CwtAbs
      Cwt_nonneg := le_trans hCwt00 (le_max_left _ _)
      sum_wt := by
        rw [hELL, hPHqfilt]
        exact le_trans (hsumwtAbs ℓ hℓ kmom hlat E.KH E.aScat hv.one_le_KH hv.a_pos)
          (le_max_right _ _)
      K₀_wt := h8wtK
      W1f := W1f
      W1_eq := hW1eq
      W1_even := hW1even
      W1_contDiff := hW1cd
      W1_le := hW1le
      W1_decay := hW1decay
      W1_grad_le := hW1grad
      aScat_le_one := ha1
      W1omegaf := W1omegaf
      W1omega_eq := fun k => by rw [hE]; rfl
      W1omega_nonneg := hW1om
      W1omega0_nonneg := by rw [hW1omeq]; exact hW1om0nn
      W1omega0_le := by
        rw [hW1omeq]
        exact le_trans hW1om0le (mul_le_mul_of_nonneg_right hCw0K hapos.le)
      fLf := fLf
      fL_eq := fun k => by rw [hE]; rfl
      fL_nonneg := hfL0
      fL_le_one := hfL1
      fL_even := hfLe
      fL_supp := hfLsup
      fL_eq_one := hfLone
      tau_eq := fun k => by rw [hE]; rfl
      A_eq := hAeq
      B_eq := hBeq
      hatChi_eq := hχεq
      hatChiSq_eq := hχ2eq
      ccrX_eq := by
        intro s k
        rw [hELL]
        exact hccrX s k
      hasKernel := hasKernel_guarded E.ell kmom F E hccrK hχ2eq hχεq haddO
      gHat := gHat
      gHat_le := fun k => le_trans (hgHatle k) (mul_le_mul_of_nonneg_right hCgK hapos.le)
      low_sum := by
        rw [hELL, hPHcom]
        exact le_trans hlow (div_le_div_of_nonneg_right hKlatK hKHa.le)
      sum_inv4 := by
        rw [hELL, hPHfilt]
        exact le_trans hinv4
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKlatK hKHpos.le) hapos.le)
      sum_inv6 := by
        rw [hELL, hPHfilt]
        exact le_trans hinv6
          (mul_le_mul_of_nonneg_right hKlatK (pow_nonneg hKHa.le 3))
      sum_inv3 := by
        rw [hELL, hPHfilt]
        refine le_trans hinv3 (mul_le_mul_of_nonneg_right hKlatK ?_)
        have := Real.log_nonneg hv.one_le_KH
        linarith
      omega_lattice := by
        rw [hW1omeq]
        refine le_trans homega' ?_
        have hellpos : 0 < E.ell := Work.BoseB7.ell_pos E hv
        have h2 : 0 ≤ E.aScat ^ 2 / E.ell := div_nonneg (sq_nonneg _) hellpos.le
        calc Cω * E.aScat ^ 2 / E.ell = Cω * (E.aScat ^ 2 / E.ell) := by ring
          _ ≤ K₀ * (E.aScat ^ 2 / E.ell) := mul_le_mul_of_nonneg_right hCωK h2
          _ = K₀ * E.aScat ^ 2 / E.ell := by ring
      sum_diff := fun R => by
        refine le_trans (hsumdiff' R) ?_
        have h2 : 0 ≤ E.aScat * (R / E.ell) ^ 4 := mul_nonneg hapos.le (hpow4 _)
        calc Cd * E.aScat * (R / E.ell) ^ 4 = Cd * (E.aScat * (R / E.ell) ^ 4) := by ring
          _ ≤ K₀ * (E.aScat * (R / E.ell) ^ 4) := mul_le_mul_of_nonneg_right hCdK h2
          _ = K₀ * E.aScat * (R / E.ell) ^ 4 := by ring
      q2exLower := fun Ψ => by rw [hW1omeq]; exact hq2 Ψ
      Calpha := Calpha
      Calpha_nonneg := hCalpha0
      halpha_lip := halpha'
      Cint := Cint
      Cint_nonneg := hCint0
      hintOne := by rw [hW1omeq]; exact hint'
      K₀_alpha := hCαK
      K₀_int := hCintK }

end Work.BoseK15
