import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkPsi6TermBound
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowF
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkRowsAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkShiftHigh_shiftF
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NSplit6
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## Linearity of the slot pairing in a constant multiple of its first argument -/

/-- `slotPairing ρ a b (c · g) f = c · slotPairing ρ a b g f`.

(Only used below to convert the statement of `fkRowDth_half`, which carries the natural
normalisation `-(1/2)` of the `(f,K)`-coefficient row, into the unnormalised target.) -/
private theorem fkRowDthRepaired_slotPairing_const_mul (ρ : ℝ → ℝ → ℝ) (a b : ℕ) (c : ℝ)
    (g f : ℝ → ℝ → ℝ) :
    Work.FTS.TransportS.slotPairing ρ a b (fun z θ => c * g z θ) f
      = c * Work.FTS.TransportS.slotPairing ρ a b g f := by
  have hfun : Work.Spaces.mixed b a (fun z θ => c * g z θ)
      = fun z θ => c * Work.Spaces.mixed b a g z θ :=
    Work.FTS.StrongPersist.H6Row6.mixed_const_mul_row c g b a
  rw [Work.FTS.TransportS.slotPairing, Work.FTS.TransportS.slotPairing, hfun]
  have hinner : ∀ z : ℝ,
      (∫ θ in Work.Spaces.Iθ, ρ z θ * (c * Work.Spaces.mixed b a g z θ)
        * Work.Spaces.mixed b a f z θ)
        = c * (∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b a g z θ
            * Work.Spaces.mixed b a f z θ) := by
    intro z
    rw [← MeasureTheory.integral_const_mul c
      (fun θ => ρ z θ * Work.Spaces.mixed b a g z θ * Work.Spaces.mixed b a f z θ)]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun θ => by ring)
  simp only [hinner]
  rw [← MeasureTheory.integral_const_mul c
    (fun z => ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed b a g z θ
      * Work.Spaces.mixed b a f z θ)]

/-! ## The two arithmetic shapes of the per-summand bound -/

/-- `A·M·S ≤ Kc·M·(1+S)` for `A ≤ Kc`, everything nonnegative. -/
private lemma fkRowDthRepaired_le_kcMul (Kc A M S : ℝ) (hA : A ≤ Kc) (hKc0 : 0 ≤ Kc) (hM0 : 0 ≤ M)
    (hS0 : 0 ≤ S) : A * M * S ≤ Kc * M * (1 + S) := by
  have h1 : A * M * S ≤ Kc * M * S :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hM0) hS0
  have h2 : Kc * M * S ≤ Kc * M * (1 + S) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hKc0 hM0)
  exact le_trans h1 h2

/-- `A·S·M ≤ Kc·M·(1+S)` for `A ≤ Kc`, everything nonnegative. -/
private lemma fkRowDthRepaired_le_kcMul' (Kc A M S : ℝ) (hA : A ≤ Kc) (hKc0 : 0 ≤ Kc) (hM0 : 0 ≤ M)
    (hS0 : 0 ≤ S) : A * S * M ≤ Kc * M * (1 + S) := by
  have h1 : A * S * M ≤ Kc * S * M :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hS0) hM0
  have h2 : Kc * S * M = Kc * M * S := by ring
  have h3 : Kc * M * S ≤ Kc * M * (1 + S) :=
    mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hKc0 hM0)
  linarith [h1, h2, h3]

/-! ## The row itself -/

/-- **The `(f, K)`-row for the angular derivative, in the normalisation `-(1/2)`.**

This is the `u = -(1/2)·(FK f)·D_θf` conjunct of the level-six `(f,K)`-row, with the
hypotheses regrouped as the datum package `T6Coef.DatData` and the case `b = 6` removed
(hence the extra hypothesis `b ≤ 5`); the proof is the assembly of

* the radial Leibniz splitting `H6Row6.fkRow_pairing_eq_sum`,
* the level-matched per-summand Cauchy–Schwarz `H6Row6.fkRow_summand_CS` together with the
  slot prices `H6Row6.domLeaf_le_row`/`H6Row6.slotIntegrable_row` (the leaf-weighted slot
  bundle), `H6Row6.fkPt_row` (the a.e. radial prices of `D_z^k (FK f)`) and
  `H6Row6.RowFKfAux.fkAbs_row` (`|FK f| ≤ C M`),
* the angular integration by parts `fk_radial_shift` for the exceptional `(k, a+b) = (0, 6)`
  summand. -/
private theorem fkRowDthRepaired_half : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → b ≤ 5 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => -(1 / 2) * Work.Construction.FK f z * Work.Spaces.Dth f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + M) ^ 2 * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨Cpt, hCptpos, hCpt⟩ := Work.FTS.StrongPersist.H6Row6.fkPt_row
  obtain ⟨Cab, hCabpos, hCab⟩ := Work.FTS.StrongPersist.H6Row6.fkAbs_row
  obtain ⟨Csh, hCshpos, hCsh⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fk_radial_shift
  -- the size of the per-summand price
  set Kc : ℝ := max (Real.sqrt Cpt) (max (Csh * Cab) Cab) + 1 with hKcdef
  have hKc0 : 0 ≤ Kc := by
    rw [hKcdef]
    have h0 : 0 ≤ max (Real.sqrt Cpt) (max (Csh * Cab) Cab) :=
      le_trans (Real.sqrt_nonneg Cpt) (le_max_left _ _)
    linarith
  have hKc1 : (1 : ℝ) ≤ Kc := by
    rw [hKcdef]
    have h0 : 0 ≤ max (Real.sqrt Cpt) (max (Csh * Cab) Cab) :=
      le_trans (Real.sqrt_nonneg Cpt) (le_max_left _ _)
    linarith
  have hsqrtKc : Real.sqrt Cpt ≤ Kc := by
    rw [hKcdef]
    linarith [le_max_left (Real.sqrt Cpt) (max (Csh * Cab) Cab),
      Real.sqrt_nonneg Cpt]
  have hCabKc : Cab ≤ Kc := by
    rw [hKcdef]
    have h1 : Cab ≤ max (Csh * Cab) Cab := le_max_right _ _
    have h2 : max (Csh * Cab) Cab ≤ max (Real.sqrt Cpt) (max (Csh * Cab) Cab) :=
      le_max_right _ _
    linarith [Real.sqrt_nonneg Cpt]
  have hCshCabKc : Csh * Cab ≤ Kc := by
    rw [hKcdef]
    have h1 : Csh * Cab ≤ max (Csh * Cab) Cab := le_max_left _ _
    have h2 : max (Csh * Cab) Cab ≤ max (Real.sqrt Cpt) (max (Csh * Cab) Cab) :=
      le_max_right _ _
    linarith [Real.sqrt_nonneg Cpt]
  refine ⟨max 1 (64 * Kc), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro α hαmem f M a b ρ hdat hab hb5 hρ
  have hα0 : 0 < α := hαmem.1
  have hα1 : α ≤ 1 := hαmem.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hdat.sm
  have h6 : Work.Spaces.HkMem α 6 f := hdat.h6
  have h7 : Work.Spaces.HkMem α 7 f := hdat.h7
  have hQ : Work.FTS.VocabO.HQo α 6 f := ⟨hdat.sm, hdat.h6⟩
  have hM : Work.FTS.Nonlin.Xn α f ≤ M := hdat.bdd
  have h4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) h6
  have hM0 : 0 ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hM
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hSq_mono6 : ∀ m : ℕ, m ≤ 6 →
      Work.Spaces.HkSq α m f ≤ Work.Spaces.HkSq α 6 f :=
    fun m hm => HkSq_mono hm h6
  have hSq_mono4 : ∀ m : ℕ, m ≤ 4 → Work.Spaces.HkSq α m f ≤ Work.Spaces.HkSq α 4 f :=
    fun m hm => HkSq_mono hm h4
  have hSq4M : Work.Spaces.HkSq α 4 f ≤ M ^ 2 := by
    have hXnSq : (Work.FTS.Nonlin.Xn α f) ^ 2 = Work.Spaces.HkSq α 4 f :=
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 4 f)
    rw [← hXnSq]
    exact pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 f) hM 2
  have hptj : ∀ j : ℕ, j ≤ 6 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (Work.Elliptic.DzdIter j (fun z => Work.Construction.FK f z) z) ^ 2
        ≤ Cpt * Work.Spaces.HkSq α (j + 1) f :=
    fun j hj => hCpt hα0 hsm h6 h7 j hj
  -- the leaf-weighted slot bundle, level-matched and with constant `1`
  have hC5 : ∀ (f' : ℝ → ℝ → ℝ) (a' a'' j : ℕ) (ρ' : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f' → Work.Spaces.HkMem α 6 f' →
      Work.FTS.TransportS.IsLeafW α a' ρ' → a' ≤ a'' → a'' + j ≤ 6 →
      MeasureTheory.IntegrableOn
          (fun z => ∫ θ in Work.Spaces.Iθ, ρ' z θ * (Work.Spaces.mixed j a'' f' z θ) ^ 2)
          Work.Spaces.Iz ∧
        (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
          (fun θ => ρ' z θ * (Work.Spaces.mixed j a'' f' z θ) ^ 2) Work.Spaces.Iθ) ∧
        (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ρ' z θ * (Work.Spaces.mixed j a'' f' z θ) ^ 2)
          ≤ Work.Spaces.HkSq α (a'' + j) f' := by
    intro f' a' a'' j ρ' hsm' h6' hρ' haa haj
    obtain ⟨hsl, hmar⟩ := Work.FTS.StrongPersist.H6Row6.slotIntegrable_row hα0 hsm' h6'
      hρ' haa haj
    have hm : Work.Spaces.HkMem α (a'' + j) f' :=
      Work.FTS.OpenPkg.HkMem_mono_open hsm' (a'' + j) haj h6'
    have haeθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := Work.FTS.IPGen.ip_ae_mem_Ioo_Iθ
    refine ⟨hsl, hmar, ?_⟩
    have hslice : ∀ z ∈ Work.Spaces.Iz,
        (∫ θ in Work.Spaces.Iθ, ρ' z θ * (Work.Spaces.mixed j a'' f' z θ) ^ 2)
          ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α (a'' + j) f' z θ := by
      intro z hz
      refine MeasureTheory.integral_mono_of_nonneg ?_ (hm.1 z hz) ?_
      · filter_upwards [haeθ] with θ hθ
        exact mul_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ' z
          ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _)
      · filter_upwards [haeθ] with θ hθ
        exact Work.FTS.StrongPersist.H6Row6.domLeaf_le_row hα0 hρ' haa (le_refl _) hz hθ
    calc (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ρ' z θ * (Work.Spaces.mixed j a'' f' z θ) ^ 2)
        ≤ ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α (a'' + j) f' z θ := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ hm.2 ?_
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
            refine MeasureTheory.integral_nonneg_of_ae ?_
            filter_upwards [haeθ] with θ hθ
            exact mul_nonneg (Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hρ' z
              ⟨hθ.1.le, hθ.2.le⟩) (sq_nonneg _)
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
            exact hslice z hz
      _ = Work.Spaces.HkSq α (a'' + j) f' := rfl
  -- the level-six form of the bundle, as required by the per-summand Cauchy–Schwarz
  have hC5_6 : ∀ (f' : ℝ → ℝ → ℝ) (a' a'' j : ℕ) (ρ' : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.SmoothOpen f' → Work.Spaces.HkMem α 6 f' →
      Work.FTS.TransportS.IsLeafW α a' ρ' → a' ≤ a'' → a'' + j ≤ 6 →
      MeasureTheory.IntegrableOn
          (fun z => ∫ θ in Work.Spaces.Iθ, ρ' z θ * (Work.Spaces.mixed j a'' f' z θ) ^ 2)
          Work.Spaces.Iz ∧
        (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn
          (fun θ => ρ' z θ * (Work.Spaces.mixed j a'' f' z θ) ^ 2) Work.Spaces.Iθ) ∧
        (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ρ' z θ * (Work.Spaces.mixed j a'' f' z θ) ^ 2) ≤ Work.Spaces.HkSq α 6 f' := by
    intro f' a' a'' j ρ' hsm' h6' hρ' haa haj
    obtain ⟨h1, h2, h3⟩ := hC5 f' a' a'' j ρ' hsm' h6' hρ' haa haj
    exact ⟨h1, h2, le_trans h3 (HkSq_mono haj h6')⟩
  -- ## the splitting
  rw [Work.FTS.StrongPersist.H6Row6.fkRow_pairing_eq_sum hα0 hα1 hsm h6 h7 hab hρ
    hCptpos hptj]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  refine le_trans (Finset.sum_le_sum
    (f := fun k => |∫ z in Work.Spaces.Iz, (-(1 / 2)) * ((b.choose k : ℝ)
        * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
            * ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
              * Work.Spaces.mixed b a f z θ))|)
    (g := fun k => (1 / 2) * (b.choose k : ℝ)
        * (Kc * M * (1 + Work.Spaces.HkSq α 6 f)))
    fun k hk => ?_) ?_
  · have hkb : k ≤ b := by have h := Finset.mem_range.mp hk; omega
    have hk5 : k ≤ 5 := by omega
    have hk6 : k ≤ 6 := by omega
    have hsplit : |∫ z in Work.Spaces.Iz, (-(1 / 2)) * ((b.choose k : ℝ)
          * (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
              * ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ))|
        = (1 / 2) * (b.choose k : ℝ)
          * |∫ z in Work.Spaces.Iz,
              Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z
              * ∫ θ in Work.Spaces.Iθ, ρ z θ * Work.Spaces.mixed (b - k) (a + 1) f z θ
                * Work.Spaces.mixed b a f z θ| := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [abs_mul, abs_mul, abs_of_neg (by norm_num : (-(1 / 2) : ℝ) < 0), neg_neg,
        abs_of_nonneg (Nat.cast_nonneg (b.choose k))]
      ring
    rw [hsplit]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    -- ## the case analysis (`k ≤ 5`, so the `k = 6` case of the general row is absent)
    rcases eq_or_ne k 0 with hk0eq | hk0ne
    · subst hk0eq
      -- the radial price of `FK f`
      have hArK : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
          |Work.Elliptic.DzdIter 0 (fun z => Work.Construction.FK f z) z| ≤ Cab * M := by
        filter_upwards
          [Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkTheta_ae_pos] with z hz
        rw [Work.Elliptic.DzdIter_zero]
        exact hCab α hαmem f M hQ h7 hM z hz
      by_cases hab5 : a + b ≤ 5
      · -- `k = 0`, `a + b ≤ 5`: the level-`6` price of the shifted slot
        have hKYv : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ρ z θ * (Work.Spaces.mixed (b - 0) (a + 1) f z θ) ^ 2)
            ≤ Work.Spaces.HkSq α 6 f := by
          exact (hC5_6 f a (a + 1) b ρ hsm h6 hρ (by omega) (by omega)).2.2
        refine le_trans (Work.FTS.StrongPersist.H6Row6.fkRow_summand_CS hαmem hsm h6 h7 hab
          (show 0 ≤ b by omega) hρ (hC5_6 f a a b ρ hsm h6 hρ (le_refl a) (by omega)).2.2
          (mul_nonneg hCabpos.le hM0) (by omega) hArK hKYv) ?_
        rw [show Cab * M * Real.sqrt (Work.Spaces.HkSq α 6 f)
              * Real.sqrt (Work.Spaces.HkSq α 6 f)
            = (Cab * M) * (Real.sqrt (Work.Spaces.HkSq α 6 f)
              * Real.sqrt (Work.Spaces.HkSq α 6 f)) by ring,
          Real.mul_self_sqrt hS0]
        exact fkRowDthRepaired_le_kcMul Kc Cab M (Work.Spaces.HkSq α 6 f) hCabKc hKc0 hM0 hS0
      · -- `k = 0`, `a + b = 6`: the angular integration by parts
        rw [Work.Elliptic.DzdIter_zero]
        have hsh := hCsh hα0 hα1 hsm h6 h7 (fun z => Work.Construction.FK f z)
          (Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fk_cont_FK hsm h4)
          (mul_nonneg hCabpos.le hM0)
          (fun z hz => hCab α hαmem f M hQ h7 hM z hz) a b ρ hab hρ
        have hkey : Csh * (Cab * M) * Work.Spaces.HkSq α 6 f
            = (Csh * Cab) * M * Work.Spaces.HkSq α 6 f := by ring
        rw [hkey] at hsh
        exact le_trans hsh (fkRowDthRepaired_le_kcMul Kc (Csh * Cab) M (Work.Spaces.HkSq α 6 f)
          hCshCabKc hKc0 hM0 hS0)
    · -- `1 ≤ k ≤ 5`
      have hk1 : 1 ≤ k := by omega
      by_cases hk3 : k ≤ 3
      · -- `1 ≤ k ≤ 3`: the radial price `√C M` and the level-price `HkSq α 6 f`
        have hArK : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
            |Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z|
              ≤ Real.sqrt Cpt * M := by
          filter_upwards [hptj k hk6] with z hz
          have h2 : Work.Spaces.HkSq α (k + 1) f ≤ M ^ 2 :=
            le_trans (hSq_mono4 (k + 1) (by omega)) hSq4M
          have h3 : (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z) ^ 2
              ≤ (Real.sqrt Cpt * M) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt hCptpos.le]
            exact le_trans hz (mul_le_mul_of_nonneg_left h2 hCptpos.le)
          have h4' : |Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z|
              ≤ Real.sqrt Cpt * M := by
            have h4'' := Real.sqrt_le_sqrt h3
            rw [Real.sqrt_sq_eq_abs,
              Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg Cpt) hM0)] at h4''
            exact h4''
          exact h4'
        have hKYv : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ρ z θ * (Work.Spaces.mixed (b - k) (a + 1) f z θ) ^ 2)
            ≤ Work.Spaces.HkSq α 6 f := by
          exact (hC5_6 f a (a + 1) (b - k) ρ hsm h6 hρ (by omega) (by omega)).2.2
        refine le_trans (Work.FTS.StrongPersist.H6Row6.fkRow_summand_CS hαmem hsm h6 h7 hab
          hkb hρ (hC5_6 f a a b ρ hsm h6 hρ (le_refl a) (by omega)).2.2
          (mul_nonneg (Real.sqrt_nonneg _) hM0) (by omega) hArK hKYv) ?_
        rw [show Real.sqrt Cpt * M * Real.sqrt (Work.Spaces.HkSq α 6 f)
              * Real.sqrt (Work.Spaces.HkSq α 6 f)
            = (Real.sqrt Cpt * M) * (Real.sqrt (Work.Spaces.HkSq α 6 f)
              * Real.sqrt (Work.Spaces.HkSq α 6 f)) by ring,
          Real.mul_self_sqrt hS0]
        exact fkRowDthRepaired_le_kcMul Kc (Real.sqrt Cpt) M (Work.Spaces.HkSq α 6 f) hsqrtKc hKc0 hM0 hS0
      · -- `4 ≤ k ≤ 5`: the radial price `√(C·HkSq α 6 f)` and the level-price `M`
        have hArK : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
            |Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z|
              ≤ Real.sqrt (Cpt * Work.Spaces.HkSq α 6 f) := by
          filter_upwards [hptj k hk6] with z hz
          have h2 : Work.Spaces.HkSq α (k + 1) f ≤ Work.Spaces.HkSq α 6 f :=
            hSq_mono6 (k + 1) (by omega)
          have h3 : (Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z) ^ 2
              ≤ (Real.sqrt (Cpt * Work.Spaces.HkSq α 6 f)) ^ 2 := by
            rw [Real.sq_sqrt (mul_nonneg hCptpos.le hS0)]
            exact le_trans hz (mul_le_mul_of_nonneg_left h2 hCptpos.le)
          have h4' : |Work.Elliptic.DzdIter k (fun z => Work.Construction.FK f z) z|
              ≤ Real.sqrt (Cpt * Work.Spaces.HkSq α 6 f) := by
            have h4'' := Real.sqrt_le_sqrt h3
            rw [Real.sqrt_sq_eq_abs,
              Real.sqrt_sq (Real.sqrt_nonneg (Cpt * Work.Spaces.HkSq α 6 f))] at h4''
            exact h4''
          exact h4'
        have hKYv : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ρ z θ * (Work.Spaces.mixed (b - k) (a + 1) f z θ) ^ 2) ≤ M ^ 2 := by
          refine le_trans (hC5 f a (a + 1) (b - k) ρ hsm h6 hρ (by omega) (by omega)).2.2 ?_
          exact le_trans (hSq_mono4 ((a + 1) + (b - k)) (by omega)) hSq4M
        refine le_trans (Work.FTS.StrongPersist.H6Row6.fkRow_summand_CS hαmem hsm h6 h7 hab
          hkb hρ (hC5_6 f a a b ρ hsm h6 hρ (le_refl a) (by omega)).2.2
          (Real.sqrt_nonneg _) (by omega) hArK hKYv) ?_
        rw [Real.sqrt_sq hM0]
        have hkey : Real.sqrt (Cpt * Work.Spaces.HkSq α 6 f)
              * Real.sqrt (Work.Spaces.HkSq α 6 f)
            = Real.sqrt Cpt * Work.Spaces.HkSq α 6 f := by
          rw [Real.sqrt_mul hCptpos.le (Work.Spaces.HkSq α 6 f), mul_assoc,
            Real.mul_self_sqrt hS0]
        rw [show Real.sqrt (Cpt * Work.Spaces.HkSq α 6 f) * M
              * Real.sqrt (Work.Spaces.HkSq α 6 f)
            = (Real.sqrt (Cpt * Work.Spaces.HkSq α 6 f)
                * Real.sqrt (Work.Spaces.HkSq α 6 f)) * M by ring, hkey]
        exact fkRowDthRepaired_le_kcMul' Kc (Real.sqrt Cpt) M (Work.Spaces.HkSq α 6 f) hsqrtKc hKc0 hM0 hS0
  · -- ## the sum and the final arithmetic
    have hchoose : ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) ≤ 64 := by
      have hb6 : b ≤ 6 := by omega
      rw [← Nat.cast_sum, Nat.sum_range_choose]
      calc (((2 : ℕ) ^ b : ℕ) : ℝ) ≤ (((2 : ℕ) ^ 6 : ℕ) : ℝ) := by
            exact_mod_cast Nat.pow_le_pow_right (by norm_num) hb6
        _ = 64 := by norm_num
    calc ∑ k ∈ Finset.range (b + 1),
            (1 / 2) * (b.choose k : ℝ) * (Kc * M * (1 + Work.Spaces.HkSq α 6 f))
        = (1 / 2) * (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ))
            * (Kc * M * (1 + Work.Spaces.HkSq α 6 f)) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ (1 / 2) * 64 * (Kc * M * (1 + Work.Spaces.HkSq α 6 f)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hchoose (by norm_num)) (by positivity)
      _ = 32 * Kc * M * (1 + Work.Spaces.HkSq α 6 f) := by ring
      _ ≤ 32 * Kc * (1 + M) ^ 2 * (1 + Work.Spaces.HkSq α 6 f) := by
          rw [show (32 : ℝ) * Kc * M * (1 + Work.Spaces.HkSq α 6 f)
                = (32 * Kc) * (M * (1 + Work.Spaces.HkSq α 6 f)) by ring,
            show (32 : ℝ) * Kc * (1 + M) ^ 2 * (1 + Work.Spaces.HkSq α 6 f)
                = (32 * Kc) * ((1 + M) ^ 2 * (1 + Work.Spaces.HkSq α 6 f)) by ring]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (by nlinarith : M ≤ (1 + M) ^ 2) (by linarith))
            (by positivity)
      _ ≤ max 1 (64 * Kc) * α ^ (-(3 : ℝ)) * (1 + M) ^ 2
            * (1 + Work.Spaces.HkSq α 6 f) := by
          have h1 : (32 : ℝ) * Kc ≤ max 1 (64 * Kc) * α ^ (-(3 : ℝ)) := by
            have ha : (1 : ℝ) ≤ α ^ (-(3 : ℝ)) :=
              Work.FTS.StrongPersist.H6Row6.one_le_rpow_neg_three_row hαmem
            have hb : (32 : ℝ) * Kc ≤ max 1 (64 * Kc) := by
              have h32 : (32 : ℝ) * Kc ≤ 64 * Kc := by linarith
              exact le_trans h32 (le_max_right _ _)
            nlinarith [hb, ha, hKc0]
          rw [show (32 : ℝ) * Kc * (1 + M) ^ 2 * (1 + Work.Spaces.HkSq α 6 f)
                = ((32 : ℝ) * Kc) * ((1 + M) ^ 2 * (1 + Work.Spaces.HkSq α 6 f)) by ring,
            show max 1 (64 * Kc) * α ^ (-(3 : ℝ)) * (1 + M) ^ 2
                * (1 + Work.Spaces.HkSq α 6 f)
                = (max 1 (64 * Kc) * α ^ (-(3 : ℝ)))
                  * ((1 + M) ^ 2 * (1 + Work.Spaces.HkSq α 6 f)) by ring]
          exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- **A repaired copy of `FkAux.fkRowDth`**: the `(FK f)·D_θf` row, `b ≤ 5`.

`|slotPairing ρ a b (fun z θ => FK f z · D_θ f z θ) f| ≤ C α^{-3}(1+M)²(1 + HkSq α 6 f)` for a
datum `DatData α f M`, `a + b ≤ 6`, `b ≤ 5` and a leaf weight `ρ` of the slot `a`.

**Why a copy:** the tree's `FkAux/fkRowDth.lean` (whose private `fkRowDth_half` is a complete
proof of this statement) **no longer compiles**, so it cannot be imported: on 2026-10-10 the
signature of `Work.FTS.StrongPersist.H6Row6.fkRow_summand_CS`
(`H6Row6/RowFKfCore2.lean`) gained an extra hypothesis
`hVf2 : ∫∫ ρ·(mixed b a f)² ≤ HkSq α 6 f` (and dropped the leaf-slot bundle `C5_6`) that
`fkRowDth.lean` still passes.  The three failing call sites are lines 260, 305 and 336 of
`fkRowDth.lean`; the repair is to replace the argument `hC5_6` in each of them by

  `(hC5_6 f a a b ρ hsm h6 hρ (le_refl a) (by omega)).2.2`

(the third conjunct of the **local** bundle `hC5_6`, with `f' := f`, `a' := a`,
`a'' := a`, `j := b`, `ρ' := ρ`, `a' ≤ a''` = `le_refl a`, `a'' + j ≤ 6` = `a + b ≤ 6`; the
bundle itself is a local hypothesis of `fkRowDth_half`'s proof and is left untouched). -/
theorem fkRowDthRepaired : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ) (a b : ℕ) (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      a + b ≤ 6 → b ≤ 5 → Work.FTS.TransportS.IsLeafW α a ρ →
      |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) f|
        ≤ C * α ^ (-(3 : ℝ)) * (1 + M) * (1 + M)
            * (1 + Work.Spaces.HkSq α 6 f) := by
  obtain ⟨C, hCpos, hC⟩ := fkRowDthRepaired_half
  refine ⟨2 * C, by positivity, ?_⟩
  intro α hαmem f M a b ρ hdat hab hb5 hleaf
  have h := hC α hαmem f M a b ρ hdat hab hb5 hleaf
  -- the `-(1/2)`-normalised pairing is half of the unnormalised one
  have hlin := fkRowDthRepaired_slotPairing_const_mul ρ a b (-2 : ℝ)
    (fun z θ => -(1 / 2) * Work.Construction.FK f z * Work.Spaces.Dth f z θ) f
  have hfun : (fun z θ => (-2 : ℝ) * (-(1 / 2) * Work.Construction.FK f z
        * Work.Spaces.Dth f z θ))
      = fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ := by
    funext z θ
    ring
  have habs : |Work.FTS.TransportS.slotPairing ρ a b
        (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth f z θ) f|
      = 2 * |Work.FTS.TransportS.slotPairing ρ a b
          (fun z θ => -(1 / 2) * Work.Construction.FK f z * Work.Spaces.Dth f z θ) f| := by
    rw [← hfun, hlin, abs_mul, abs_of_neg (by norm_num : (-2 : ℝ) < 0)]
    ring
  rw [habs]
  refine le_trans (mul_le_mul_of_nonneg_left h (by norm_num)) ?_
  refine le_of_eq ?_
  ring

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
