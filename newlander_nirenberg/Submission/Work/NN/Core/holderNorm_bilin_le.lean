import Mathlib
import Submission.Work.CR.Flat.Holder.hSN_bilinear_le
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Core

open Work.CR.Flat.Holder

universe u v uX uE uF

/-! ### A `hSN` bilinear Leibniz bound with independent universes

`Work.CR.Flat.Holder.hSN_bilinear_le` requires the domain `D` and the coefficient spaces
`E F G` to live in a *common* universe (the induction proceeds through the spaces of
continuous linear maps, which step up the universe otherwise).  We need the bound with the
domain in a possibly smaller universe; the same proof goes through verbatim for the
signature `{D : Type u} {E F G : Type (max u v)}`, and we record it here. -/

lemma hSN_bilinear_aux_gen (α : ℝ) :
    ∀ (n : ℕ) {D : Type u} {E F G : Type (max u v)} [NormedAddCommGroup D] [NormedSpace ℝ D]
      [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
      [NormedAddCommGroup G] [NormedSpace ℝ G] (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F}
      {Ω : Set D}, ContDiffOn ℝ n f Ω → ContDiffOn ℝ n g Ω → UniqueDiffOn ℝ Ω →
      hSN n α (fun x => B (f x) (g x)) Ω ≤ ENNReal.ofReal ‖B‖ * bilinRHS α n f g Ω := by
  intro n
  induction n with
  | zero =>
    intro D E F G _ _ _ _ _ _ _ _ B f g Ω _ _ _
    exact hSN_zero_bilinear_le α B
  | succ k ih =>
    intro D E F G _ _ _ _ _ _ _ _ B f g Ω hf hg hΩ
    have hderiv : (k : WithTop ℕ∞) + 1 ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by
      simp only [Nat.cast_succ, le_refl]
    have hfk : ContDiffOn ℝ k f Ω := hf.of_le (Nat.cast_le.2 (Nat.le_succ k))
    have hgk : ContDiffOn ℝ k g Ω := hg.of_le (Nat.cast_le.2 (Nat.le_succ k))
    have hDg : ContDiffOn ℝ k (fun z => fderivWithin ℝ g Ω z) Ω := hg.fderivWithin hΩ hderiv
    have hDf : ContDiffOn ℝ k (fun z => fderivWithin ℝ f Ω z) Ω := hf.fderivWithin hΩ hderiv
    have hG1 : ContDiffOn ℝ k (fun z => (B.precompR D) (f z) (fderivWithin ℝ g Ω z)) Ω :=
      (B.precompR D).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hfk hDg
    have hG2 : ContDiffOn ℝ k (fun z => (B.precompL D) (fderivWithin ℝ f Ω z) (g z)) Ω :=
      (B.precompL D).isBoundedBilinearMap.contDiff.comp₂_contDiffOn hDf hgk
    have hI1 : hSN k α (fun z => (B.precompR D) (f z) (fderivWithin ℝ g Ω z)) Ω
        ≤ ENNReal.ofReal ‖B‖ * bilinRHS α k f (fun z => fderivWithin ℝ g Ω z) Ω :=
      (ih (F := D →L[ℝ] F) (G := D →L[ℝ] G) (B := B.precompR D) hfk hDg hΩ).trans (by
        gcongr
        exact B.norm_precompR_le D)
    have hI2 : hSN k α (fun z => (B.precompL D) (fderivWithin ℝ f Ω z) (g z)) Ω
        ≤ ENNReal.ofReal ‖B‖ * bilinRHS α k (fun z => fderivWithin ℝ f Ω z) g Ω :=
      (ih (E := D →L[ℝ] E) (G := D →L[ℝ] G) (B := B.precompL D) hDf hgk hΩ).trans (by
        gcongr
        exact B.norm_precompL_le D)
    calc hSN (k + 1) α (fun x => B (f x) (g x)) Ω
        = hSN k α (fun z => fderivWithin ℝ (fun x => B (f x) (g x)) Ω z) Ω :=
          (hSN_fderivWithin k α (fun x => B (f x) (g x)) Ω hΩ).symm
      _ = hSN k α ((fun z => (B.precompR D) (f z) (fderivWithin ℝ g Ω z))
            + (fun z => (B.precompL D) (fderivWithin ℝ f Ω z) (g z))) Ω := by
          refine hSN_congr fun z hz => ?_
          exact B.fderivWithin_of_bilinear (hf.differentiableOn (by positivity) z hz)
            (hg.differentiableOn (by positivity) z hz) (hΩ z hz)
      _ ≤ hSN k α (fun z => (B.precompR D) (f z) (fderivWithin ℝ g Ω z)) Ω
            + hSN k α (fun z => (B.precompL D) (fderivWithin ℝ f Ω z) (g z)) Ω :=
          hSN_add_le (φ := fun z => (B.precompR D) (f z) (fderivWithin ℝ g Ω z))
            (ψ := fun z => (B.precompL D) (fderivWithin ℝ f Ω z) (g z)) k α hG1 hG2 hΩ
      _ ≤ ENNReal.ofReal ‖B‖ * bilinRHS α k f (fun z => fderivWithin ℝ g Ω z) Ω
            + ENNReal.ofReal ‖B‖ * bilinRHS α k (fun z => fderivWithin ℝ f Ω z) g Ω :=
          add_le_add hI1 hI2
      _ = ENNReal.ofReal ‖B‖ * bilinRHS α (k + 1) f g Ω := by
          rw [← mul_add, bilinRHS_fderiv_step α k hΩ]

/-- The sum form of `hSN_bilinear_aux_gen`, for the signature with independent universes. -/
theorem hSN_bilinear_le_gen {D : Type u} {E F G : Type (max u v)}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (n : ℕ) (α : ℝ) (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F} {Ω : Set D}
    (hf : ContDiffOn ℝ n f Ω) (hg : ContDiffOn ℝ n g Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    hSN n α (fun x => B (f x) (g x)) Ω
      ≤ ENNReal.ofReal ‖B‖ * ∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ENNReal) *
          (hSN i α f Ω * iDN (n - i) g Ω + iDN i f Ω * hSN (n - i) α g Ω) := by
  change hSN n α (fun x => B (f x) (g x)) Ω ≤ ENNReal.ofReal ‖B‖ * bilinRHS α n f g Ω
  exact hSN_bilinear_aux_gen α n B hf hg hΩ

/-! ### The elementary `ℝ≥0∞` inequality behind the Leibniz grouping -/

lemma mul_add_le_mul_add (a b c d : ℝ≥0∞) :
    a * c + (b * c + a * d) ≤ (a + b) * (c + d) := by
  calc a * c + (b * c + a * d) = (a * c + b * c) + a * d := by ac_rfl
    _ ≤ (a * c + b * c) + (a * d + b * d) := by
        gcongr
        exact le_add_right le_rfl
    _ = (a + b) * (c + d) := by rw [mul_add, add_mul, add_mul]

/-! ### The main estimate -/

lemma holderNorm_bilin_le_aux {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (m : ℕ) (α : ℝ) (B : E →L[ℝ] F →L[ℝ] ℂ) {f : X → E} {g : X → F} {Ω : Set X}
    (hf : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) f Ω)
    (hg : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) g Ω) (hΩ : UniqueDiffOn ℝ Ω)
    {A E' : ENNReal}
    (hA : ∀ l, l ≤ m → iDN l f Ω + hSN l α f Ω ≤ A)
    (hE : ∀ l, l ≤ m → iDN l g Ω + hSN l α g Ω ≤ E') :
    Work.CR.Flat.holderNorm m α (fun x => B (f x) (g x)) Ω
      ≤ ENNReal.ofReal ‖B‖ * (ENNReal.ofReal (3 * ((m : ℝ) + 1) * 2 ^ m) * (A * E')) := by
  -- Lift the coefficient spaces into a common (large) universe, keeping the domain fixed.
  let EU := ULift.{max uX uE uF, uE} E
  let FU := ULift.{max uX uE uF, uF} F
  let CU := ULift.{max uX uE uF, 0} ℂ
  let eE : E ≃ₗᵢ[ℝ] EU := (LinearIsometryEquiv.ulift ℝ E).symm
  let eF : F ≃ₗᵢ[ℝ] FU := (LinearIsometryEquiv.ulift ℝ F).symm
  let eC : ℂ ≃ₗᵢ[ℝ] CU := (LinearIsometryEquiv.ulift ℝ ℂ).symm
  let fU : X → EU := fun x => eE (f x)
  let gU : X → FU := fun x => eF (g x)
  let iE : EU →L[ℝ] E := eE.symm
  let iF : FU →L[ℝ] F := eF.symm
  let jC : ℂ →L[ℝ] CU := eC
  let BU : EU →L[ℝ] FU →L[ℝ] CU :=
    ContinuousLinearMap.compL ℝ EU (FU →L[ℝ] ℂ) (FU →L[ℝ] CU)
      (ContinuousLinearMap.compL ℝ FU ℂ CU jC)
      (((B.comp iE).flip.comp iF).flip)
  have hBU_apply : ∀ a b, BU a b = jC (B (iE a) (iF b)) := by
    intro a b
    simp only [BU, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.comp_apply]
  have hBU_norm : ‖BU‖ ≤ ‖B‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B) fun a => ?_
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun b => ?_
    rw [hBU_apply a b]
    calc ‖jC (B (iE a) (iF b))‖ = ‖B (iE a) (iF b)‖ := by
          change ‖eC (B (iE a) (iF b))‖ = ‖B (iE a) (iF b)‖
          exact eC.norm_map _
      _ ≤ ‖B‖ * ‖iE a‖ * ‖iF b‖ := B.le_opNorm₂ _ _
      _ = ‖B‖ * ‖a‖ * ‖b‖ := by
          rw [show ‖iE a‖ = ‖a‖ from by
                change ‖eE.symm a‖ = ‖a‖
                exact eE.symm.norm_map a,
              show ‖iF b‖ = ‖b‖ from by
                change ‖eF.symm b‖ = ‖b‖
                exact eF.symm.norm_map b]
  have hfm : ∀ i, i ≤ m → ContDiffOn ℝ i f Ω := fun i hi => hf.of_le (Nat.cast_le.2 hi)
  have hgm : ∀ i, i ≤ m → ContDiffOn ℝ i g Ω := fun i hi => hg.of_le (Nat.cast_le.2 hi)
  have hfUm : ∀ i, i ≤ m → ContDiffOn ℝ i fU Ω := fun i hi => contDiffOn_comp_lie eE (hfm i hi)
  have hgUm : ∀ i, i ≤ m → ContDiffOn ℝ i gU Ω := fun i hi => contDiffOn_comp_lie eF (hgm i hi)
  have hIF : ∀ j, iDN j fU Ω = iDN j f Ω := fun j => iDN_comp_lie eE f j Ω hΩ
  have hSF : ∀ j, hSN j α fU Ω = hSN j α f Ω := fun j => hSN_comp_lie eE f j α Ω hΩ
  have hIG : ∀ j, iDN j gU Ω = iDN j g Ω := fun j => iDN_comp_lie eF g j Ω hΩ
  have hSG : ∀ j, hSN j α gU Ω = hSN j α g Ω := fun j => hSN_comp_lie eF g j α Ω hΩ
  have hprod : (fun x => BU (fU x) (gU x)) = fun x => eC (B (f x) (g x)) := by
    funext x
    rw [hBU_apply]
    change eC (B (eE.symm (fU x)) (eF.symm (gU x))) = eC (B (f x) (g x))
    rw [show eE.symm (fU x) = f x from by
          change eE.symm (eE (f x)) = f x
          exact eE.symm_apply_apply (f x),
        show eF.symm (gU x) = g x from by
          change eF.symm (eF (g x)) = g x
          exact eF.symm_apply_apply (g x)]
  -- the Hölder-seminorm bound at each level
  have hSprod : ∀ i, i ≤ m → hSN i α (fun x => B (f x) (g x)) Ω ≤
      ENNReal.ofReal ‖B‖ * (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
        (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω)) := by
    intro i hi
    have hb := hSN_bilinear_le_gen.{uX, max uE uF} (n := i) (α := α) (B := BU)
      (f := fU) (g := gU) (Ω := Ω) (hfUm i hi) (hgUm i hi) hΩ
    have hL : hSN i α (fun x => BU (fU x) (gU x)) Ω
        = hSN i α (fun x => B (f x) (g x)) Ω := by
      rw [hprod, hSN_comp_lie eC (fun x => B (f x) (g x)) i α Ω hΩ]
    have hR : (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (hSN j α fU Ω * iDN (i - j) gU Ω + iDN j fU Ω * hSN (i - j) α gU Ω))
        = ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
          (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hSF j, hIG (i - j), hIF j, hSG (i - j)]
    rw [hL, hR] at hb
    exact hb.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal hBU_norm) _)
  have hchoose : ∀ i : ℕ,
      (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞)) = (2 : ℝ≥0∞) ^ i :=
    fun i => by exact_mod_cast Nat.sum_range_choose i
  -- the level bound
  have key : ∀ i, i ≤ m →
      iDN i (fun x => B (f x) (g x)) Ω + hSN i α (fun x => B (f x) (g x)) Ω
        ≤ ENNReal.ofReal ‖B‖ * ((2 : ℝ≥0∞) ^ i * (A * E')) := by
    intro i hi
    have hI := iDN_bilinear_le (B := B) i (hfm i hi) (hgm i hi) hΩ
    have hH := hSprod i hi
    have hstep : (∑ j ∈ Finset.range (i + 1),
            (i.choose j : ℝ≥0∞) * (iDN j f Ω * iDN (i - j) g Ω))
        + (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
            (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω))
        ≤ (2 : ℝ≥0∞) ^ i * (A * E') := by
      rw [← Finset.sum_add_distrib]
      calc ∑ j ∈ Finset.range (i + 1),
              ((i.choose j : ℝ≥0∞) * (iDN j f Ω * iDN (i - j) g Ω)
                + (i.choose j : ℝ≥0∞) * (hSN j α f Ω * iDN (i - j) g Ω
                    + iDN j f Ω * hSN (i - j) α g Ω))
          ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) * (A * E') := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj' : j ≤ m := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hi
            have hji : i - j ≤ m := le_trans (Nat.sub_le i j) hi
            rw [← mul_add]
            gcongr
            calc iDN j f Ω * iDN (i - j) g Ω
                  + (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω)
                ≤ (iDN j f Ω + hSN j α f Ω) * (iDN (i - j) g Ω + hSN (i - j) α g Ω) :=
                  mul_add_le_mul_add _ _ _ _
              _ ≤ A * E' := mul_le_mul' (hA j hj') (hE (i - j) hji)
        _ = (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞)) * (A * E') := by
            rw [Finset.sum_mul]
        _ = (2 : ℝ≥0∞) ^ i * (A * E') := by rw [hchoose i]
    calc iDN i (fun x => B (f x) (g x)) Ω + hSN i α (fun x => B (f x) (g x)) Ω
        ≤ ENNReal.ofReal ‖B‖ * (∑ j ∈ Finset.range (i + 1),
              (i.choose j : ℝ≥0∞) * (iDN j f Ω * iDN (i - j) g Ω))
          + ENNReal.ofReal ‖B‖ * (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
              (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω)) :=
          add_le_add hI hH
      _ = ENNReal.ofReal ‖B‖ * ((∑ j ∈ Finset.range (i + 1),
              (i.choose j : ℝ≥0∞) * (iDN j f Ω * iDN (i - j) g Ω))
          + (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ≥0∞) *
              (hSN j α f Ω * iDN (i - j) g Ω + iDN j f Ω * hSN (i - j) α g Ω))) :=
          (mul_add _ _ _).symm
      _ ≤ ENNReal.ofReal ‖B‖ * ((2 : ℝ≥0∞) ^ i * (A * E')) :=
          mul_le_mul' le_rfl hstep
  have hsum_le : (∑ i ∈ Finset.range (m + 1), (2 : ℝ≥0∞) ^ i)
      ≤ ENNReal.ofReal (3 * ((m : ℝ) + 1) * 2 ^ m) := by
    have hofReal : ((m : ℝ≥0∞) + 1) * 2 ^ m = ENNReal.ofReal (((m : ℝ) + 1) * 2 ^ m) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (by positivity) (by norm_num),
        ENNReal.ofReal_natCast, ENNReal.ofReal_one, ENNReal.ofReal_pow (by norm_num)]
      norm_num
    calc (∑ i ∈ Finset.range (m + 1), (2 : ℝ≥0∞) ^ i)
        ≤ ∑ i ∈ Finset.range (m + 1), (2 : ℝ≥0∞) ^ m :=
          Finset.sum_le_sum fun i hi =>
            pow_le_pow_right₀ (by norm_num) (by have := Finset.mem_range.mp hi; omega)
      _ = (m + 1) • (2 : ℝ≥0∞) ^ m := by rw [Finset.sum_const, Finset.card_range]
      _ = ((m : ℝ≥0∞) + 1) * 2 ^ m := by rw [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      _ = ENNReal.ofReal (((m : ℝ) + 1) * 2 ^ m) := hofReal
      _ ≤ ENNReal.ofReal (3 * ((m : ℝ) + 1) * 2 ^ m) := by
          apply ENNReal.ofReal_le_ofReal
          rw [show (3 : ℝ) * ((m : ℝ) + 1) * 2 ^ m = 3 * (((m : ℝ) + 1) * 2 ^ m) from by ring]
          exact le_mul_of_one_le_left (by positivity) (by norm_num)
  calc Work.CR.Flat.holderNorm m α (fun x => B (f x) (g x)) Ω
      = ∑ i ∈ Finset.range (m + 1),
          (iDN i (fun x => B (f x) (g x)) Ω + hSN i α (fun x => B (f x) (g x)) Ω) := rfl
    _ ≤ ∑ i ∈ Finset.range (m + 1), ENNReal.ofReal ‖B‖ * ((2 : ℝ≥0∞) ^ i * (A * E')) :=
        Finset.sum_le_sum fun i hi => key i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    _ = ENNReal.ofReal ‖B‖ * ((∑ i ∈ Finset.range (m + 1), (2 : ℝ≥0∞) ^ i) * (A * E')) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [← Finset.sum_mul]
    _ ≤ ENNReal.ofReal ‖B‖ * (ENNReal.ofReal (3 * ((m : ℝ) + 1) * 2 ^ m) * (A * E')) :=
        mul_le_mul' le_rfl (mul_le_mul_left hsum_le (A * E'))

lemma holderNorm_bilin_le {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (m : ℕ) (α : ℝ) (B : E →L[ℝ] F →L[ℝ] ℂ) {f : X → E} {g : X → F} {Ω : Set X} (hf : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) f Ω) (hg : ContDiffOn ℝ ((m : ℕ) : WithTop ℕ∞) g Ω) (hΩ : UniqueDiffOn ℝ Ω) {A E' : ENNReal} (hA : ∀ l, l ≤ m → Work.CR.Flat.Holder.iDN l f Ω + Work.CR.Flat.Holder.hSN l α f Ω ≤ A) (hE : ∀ l, l ≤ m → Work.CR.Flat.Holder.iDN l g Ω + Work.CR.Flat.Holder.hSN l α g Ω ≤ E') : Work.CR.Flat.holderNorm m α (fun x => B (f x) (g x)) Ω ≤ ENNReal.ofReal ‖B‖ * (ENNReal.ofReal (3 * ((m : ℝ) + 1) * 2 ^ m) * (A * E')) :=
  holderNorm_bilin_le_aux m α B hf hg hΩ hA hE

end Work.NN.Core
