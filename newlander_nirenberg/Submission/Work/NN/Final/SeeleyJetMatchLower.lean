/-
Jet matching from below at the hyperplane for the flat Seeley extension.
-/
import Mathlib
import Submission.Work.NN.Final.SeeleyLoc
import Submission.Work.NN.Final.seeleyLoc_iteratedFDeriv_eq_tsum

noncomputable section

open scoped NNReal ENNReal ContDiff Topology BigOperators
open Set Filter

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.NN.Final.JetMatch

open Work.NN.Final

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## Bounds for the cutoff factor -/

/-- Uniform bound for the iterated derivative of the cutoff in the normal variable. -/
lemma seeleyCut_iteratedFDeriv_snd_le (i : ℕ) (x : E × ℝ) :
    ‖iteratedFDeriv ℝ i (fun y : E × ℝ => seeleyCut y.2) x‖ ≤ seeleyCutB i := by
  have h1 : (fun y : E × ℝ => seeleyCut y.2)
      = seeleyCut ∘ (ContinuousLinearMap.snd ℝ E ℝ) := rfl
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.snd ℝ E ℝ)
    seeleyCut_contDiff x (WithTop.coe_le_coe.mpr le_top)]
  have hsnd : (ContinuousLinearMap.snd ℝ E ℝ) x = x.2 := rfl
  have hprod : (∏ _ : Fin i, ‖(ContinuousLinearMap.snd ℝ E ℝ)‖) ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ E ℝ)
  calc ‖(iteratedFDeriv ℝ i seeleyCut ((ContinuousLinearMap.snd ℝ E ℝ) x)).compContinuousLinearMap
        (fun _ : Fin i => (ContinuousLinearMap.snd ℝ E ℝ))‖
      ≤ ‖iteratedFDeriv ℝ i seeleyCut x.2‖ * (∏ _ : Fin i, ‖(ContinuousLinearMap.snd ℝ E ℝ)‖) := by
        refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) (le_of_eq ?_)
        rw [hsnd]
    _ ≤ seeleyCutB i := by
        calc ‖iteratedFDeriv ℝ i seeleyCut x.2‖ * (∏ _ : Fin i, ‖(ContinuousLinearMap.snd ℝ E ℝ)‖)
            ≤ seeleyCutB i * 1 := mul_le_mul (norm_iteratedFDeriv_seeleyCut_le i x.2) hprod
              (by positivity) (seeleyCutB_nonneg i)
          _ = seeleyCutB i := mul_one _

/-- Uniform bound for the iterated derivative of the cutoff composed with the normal shear
`y ↦ -(b) * y.2`. -/
lemma seeleyCut_iteratedFDeriv_shear_le {b : ℝ} (hb : 1 ≤ b) (i : ℕ) (x : E × ℝ) :
    ‖iteratedFDeriv ℝ i (fun y : E × ℝ => seeleyCut (-b * y.2)) x‖ ≤ seeleyCutB i * b ^ i := by
  have hf : ContDiff ℝ ∞ (fun z : E × ℝ => seeleyCut z.2) := seeleyCut_contDiff.comp contDiff_snd
  have hcomp : (fun y : E × ℝ => seeleyCut (-b * y.2))
      = (fun z : E × ℝ => seeleyCut z.2) ∘ seeleyLam (X := E) (-b) := by
    funext y
    rw [Function.comp_apply, seeleyLam_apply]
  rw [hcomp, ContinuousLinearMap.iteratedFDeriv_comp_right (seeleyLam (X := E) (-b)) hf x
    (WithTop.coe_le_coe.mpr le_top)]
  have hmax : max 1 |(-b : ℝ)| = b := by
    rw [abs_neg, abs_of_nonneg (by linarith)]
    exact max_eq_right hb
  have hprod : (∏ _ : Fin i, ‖seeleyLam (X := E) (-b)‖) ≤ b ^ i := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    calc ‖seeleyLam (X := E) (-b)‖ ^ i ≤ (max 1 |(-b : ℝ)|) ^ i :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_seeleyLam_le (-b)) i
      _ = b ^ i := by rw [hmax]
  calc ‖(iteratedFDeriv ℝ i (fun z : E × ℝ => seeleyCut z.2)
          (seeleyLam (X := E) (-b) x)).compContinuousLinearMap (fun _ : Fin i => seeleyLam (X := E) (-b))‖
      ≤ ‖iteratedFDeriv ℝ i (fun z : E × ℝ => seeleyCut z.2) (seeleyLam (X := E) (-b) x)‖
          * (∏ _ : Fin i, ‖seeleyLam (X := E) (-b)‖) :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ seeleyCutB i * b ^ i :=
        mul_le_mul (seeleyCut_iteratedFDeriv_snd_le i _) hprod (by positivity)
          (seeleyCutB_nonneg i)

/-! ## The Seeley term as a shear of `g` -/

/-- The `m`-th Seeley term is the product of the scalar cutoff factor `p ↦ a m * χ (-(b m) * p.2)`
with the shear of `g`. -/
lemma seeleyTerm_eq_smul_shear (a b : ℕ → ℝ) (g : E × ℝ → ℂ) (m : ℕ) :
    seeleyTerm a b g m
      = fun y : E × ℝ => (a m * seeleyCut (-(b m) * y.2) : ℝ) • g (y.1, -(b m) * y.2) := by
  funext y
  show (a m) • (seeleyCut (-(b m) * y.2) • g (y.1, -(b m) * y.2)) = _
  rw [smul_smul]

/-- Near a point where the cutoff is `1`, the `m`-th Seeley term is the shear of `g`. -/
lemma seeleyTerm_eventuallyEq_smul_shear {a b : ℕ → ℝ} {g : E × ℝ → ℂ} {m : ℕ} {x : E × ℝ}
    (hx : |-(b m) * x.2| < 1) :
    seeleyTerm a b g m =ᶠ[𝓝 x] fun y : E × ℝ => (a m) • g (y.1, -(b m) * y.2) := by
  have hcont : Continuous fun y : E × ℝ => |-(b m) * y.2| := by
    exact continuous_abs.comp (continuous_const.mul continuous_snd)
  have hneigh : {y : E × ℝ | |-(b m) * y.2| < 1} ∈ 𝓝 x :=
    (isOpen_lt hcont continuous_const).mem_nhds hx
  filter_upwards [hneigh] with y hy
  show (a m) • (seeleyCut (-(b m) * y.2) • g (y.1, -(b m) * y.2))
      = (a m) • g (y.1, -(b m) * y.2)
  rw [seeleyCut_eq_one_of_abs_lt_one hy, one_smul]

/-! ## The chain rule for a single Seeley term -/

/-- Chain rule for the `m`-th Seeley term at a point of the lower half space where the cutoff
equals `1`: the iterated derivative of the term is the `a m`-multiple of the sheared derivative
of `g`. -/
lemma iteratedFDeriv_seeleyTerm_eq_comp_shear {W : Set E} (hW : IsOpen W) {a b : ℕ → ℝ}
    (hb1 : ∀ m, 1 ≤ b m) {i : ℕ} {g : E × ℝ → ℂ}
    (hg : ContDiffOn ℝ (i : WithTop ENat) g (seHp W))
    {m : ℕ} {x : E × ℝ} (hxW : x.1 ∈ W) (hx2 : x.2 < 0)
    (hx : |-(b m) * x.2| < 1) :
    iteratedFDeriv ℝ i (seeleyTerm a b g m) x
      = (a m) • ((iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) x)).compContinuousLinearMap
          (fun _ => seeleyLam (X := E) (-(b m)))) := by
  rw [((seeleyTerm_eventuallyEq_smul_shear hx).iteratedFDeriv ℝ i).eq_of_nhds]
  set Ω : Set (E × ℝ) := {y : E × ℝ | y.1 ∈ W ∧ |-(b m) * y.2| < 1 ∧ y.2 < 0} with hΩdef
  have hcx : Continuous fun y : E × ℝ => |-(b m) * y.2| :=
    continuous_abs.comp (continuous_const.mul continuous_snd)
  have hΩ : IsOpen Ω := by
    have h1 : Ω = (fun y : E × ℝ => |-(b m) * y.2|) ⁻¹' Set.Iio 1
        ∩ ((fun y : E × ℝ => y.2) ⁻¹' Set.Iio 0 ∩ (fun y : E × ℝ => y.1) ⁻¹' W) := by
      ext y
      simp only [hΩdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio]
      tauto
    rw [h1]
    exact ((isOpen_Iio.preimage hcx).inter ((isOpen_Iio.preimage continuous_snd).inter
      (hW.preimage continuous_fst)))
  have hxΩ : x ∈ Ω := ⟨hxW, hx, hx2⟩
  have hbpos : (0 : ℝ) < b m := by linarith [hb1 m]
  have hsub : (fun p : E × ℝ => (p.1, -(b m) * p.2)) '' Ω ⊆ seUp W := by
    rintro q ⟨p, hp, rfl⟩
    rw [hΩdef] at hp
    exact mem_seUp.mpr ⟨hp.1, mul_pos_of_neg_of_neg (by linarith) hp.2.2⟩
  have hcr := iteratedFDeriv_comp_shear_of_contDiffOn (c := -(b m))
    (by linarith : (-(b m)) ≠ 0) (isOpen_seUp hW) hΩ hsub (hg.mono seUp_subset_seHp) hxΩ
  have hpt : (x.1, -(b m) * x.2) ∈ seUp W := hsub ⟨x, hxΩ, rfl⟩
  have hsmul : iteratedFDeriv ℝ i (fun y : E × ℝ => (a m) • g (y.1, -(b m) * y.2)) x
      = (a m) • iteratedFDeriv ℝ i (fun y : E × ℝ => g (y.1, -(b m) * y.2)) x := by
    refine iteratedFDeriv_const_smul_apply' (f := fun y : E × ℝ => g (y.1, -(b m) * y.2)) ?_
    have hlin : ContDiffAt ℝ (i : WithTop ENat) (fun y : E × ℝ => (y.1, -(b m) * y.2)) x := by
      have : ContDiff ℝ (i : WithTop ENat) (fun y : E × ℝ => (y.1, -(b m) * y.2)) := by fun_prop
      exact this.contDiffAt
    exact (hg.contDiffAt (Filter.mem_of_superset ((isOpen_seUp hW).mem_nhds hpt)
      seUp_subset_seHp)).comp x hlin
  rw [hsmul, hcr]

/-! ## The uniform bound for a single Seeley term -/

/-- Uniform (in the point of the lower half space) bound for the `i`-th iterated derivative of the
`m`-th Seeley term, with the dependence on `m` isolated as `|a m| * (b m)^i`. -/
lemma norm_iteratedFDeriv_seeleyTerm_le {W : Set E} (hW : IsOpen W) {i : ℕ} {a b : ℕ → ℝ}
    (hb1 : ∀ m, 1 ≤ b m) {g : E × ℝ → ℂ} (hg : ContDiffOn ℝ (i : WithTop ENat) g (seHp W))
    {R : ℝ} (hR : ∀ z ∈ seUp W, ∀ j ≤ i, ‖iteratedFDeriv ℝ j g z‖ ≤ R)
    {m : ℕ} {x : E × ℝ} (hxW : x.1 ∈ W) (hx2 : x.2 < 0) :
    ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) x‖
      ≤ |a m| * (b m) ^ i * ((∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j) * R) := by
  have hbm1 : 1 ≤ b m := hb1 m
  have hbm0 : (0 : ℝ) < b m := lt_of_lt_of_le one_pos hbm1
  set s : Set (E × ℝ) := {y : E × ℝ | y.1 ∈ W ∧ y.2 < 0} with hsdef
  have hs : IsOpen s := by
    have h1 : s = (fun y : E × ℝ => y.2) ⁻¹' Set.Iio 0 ∩ (fun y : E × ℝ => y.1) ⁻¹' W := by
      ext y
      simp only [hsdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio]
      tauto
    rw [h1]
    exact (isOpen_Iio.preimage continuous_snd).inter (hW.preimage continuous_fst)
  have hxs : x ∈ s := ⟨hxW, hx2⟩
  set f₁ : E × ℝ → ℝ := (a m) • (fun y : E × ℝ => seeleyCut (-(b m) * y.2)) with hf₁
  set f₂ : E × ℝ → ℂ := fun y => g (y.1, -(b m) * y.2) with hf₂
  have hterm : seeleyTerm a b g m = fun y : E × ℝ => f₁ y • f₂ y := by
    rw [seeleyTerm_eq_smul_shear a b g m]
    funext y
    simp only [hf₁, hf₂, Pi.smul_apply, smul_eq_mul]
  have h₁ : ContDiff ℝ (i : WithTop ENat) f₁ := by
    rw [hf₁]
    have hcut : ContDiff ℝ (i : WithTop ENat) (fun y : E × ℝ => seeleyCut (-(b m) * y.2)) := by
      have h2 : ContDiff ℝ ∞ (fun y : E × ℝ => -(b m) * y.2) := by fun_prop
      exact (seeleyCut_contDiff.comp h2).of_le (by simp)
    exact hcut.const_smul (a m)
  have hsubs : (fun p : E × ℝ => (p.1, -(b m) * p.2)) '' s ⊆ seUp W := by
    rintro q ⟨p, hp, rfl⟩
    rw [hsdef] at hp
    exact mem_seUp.mpr ⟨hp.1, mul_pos_of_neg_of_neg (by linarith) hp.2⟩
  have h₂ : ContDiffOn ℝ (i : WithTop ENat) f₂ s := by
    rw [hf₂]
    have hlin : ContDiffOn ℝ (i : WithTop ENat) (fun y : E × ℝ => (y.1, -(b m) * y.2)) s :=
      (by fun_prop : ContDiff ℝ (i : WithTop ENat)
        (fun y : E × ℝ => (y.1, -(b m) * y.2))).contDiffOn
    have hmap : MapsTo (fun y : E × ℝ => (y.1, -(b m) * y.2)) s (seUp W) :=
      fun y hy => hsubs ⟨y, hy, rfl⟩
    exact (hg.mono seUp_subset_seHp).comp hlin hmap
  have hleib := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (f := f₁) (g := f₂) (s := s)
    (N := (i : WithTop ENat)) h₁.contDiffOn h₂ hs.uniqueDiffOn hxs le_rfl
  have hwithin : iteratedFDerivWithin ℝ i (fun y : E × ℝ => f₁ y • f₂ y) s x
      = iteratedFDeriv ℝ i (seeleyTerm a b g m) x := by
    rw [iteratedFDerivWithin_of_isOpen i hs hxs, ← hterm]
  rw [hwithin] at hleib
  refine hleib.trans ?_
  have hbound1 : ∀ j ∈ Finset.range (i + 1),
      ‖iteratedFDerivWithin ℝ j f₁ s x‖ ≤ |a m| * (seeleyCutB j * (b m) ^ j) := by
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hs hxs, hf₁]
    have hcd : ContDiffAt ℝ (j : WithTop ENat) (fun y : E × ℝ => seeleyCut (-(b m) * y.2)) x := by
      have h2 : ContDiff ℝ ∞ (fun y : E × ℝ => -(b m) * y.2) := by fun_prop
      exact ((seeleyCut_contDiff.comp h2).of_le (by simp)).contDiffAt
    rw [iteratedFDeriv_const_smul_apply (f := fun y : E × ℝ => seeleyCut (-(b m) * y.2)) hcd,
      norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (seeleyCut_iteratedFDeriv_shear_le hbm1 j x) (abs_nonneg _)
  have hbound2 : ∀ j ∈ Finset.range (i + 1),
      ‖iteratedFDerivWithin ℝ (i - j) f₂ s x‖ ≤ R * (b m) ^ (i - j) := by
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen (i - j) hs hxs, hf₂]
    have huj : ContDiffOn ℝ (((i - j : ℕ)) : WithTop ENat) g (seUp W) :=
      (hg.mono seUp_subset_seHp).of_le (by exact_mod_cast Nat.sub_le i j)
    have hcr := iteratedFDeriv_comp_shear_of_contDiffOn (c := -(b m))
      (by linarith : (-(b m)) ≠ 0) (isOpen_seUp hW) hs hsubs huj hxs
    rw [hcr]
    calc ‖(iteratedFDeriv ℝ (i - j) g (seeleyLam (X := E) (-(b m)) x)).compContinuousLinearMap
            (fun _ => seeleyLam (X := E) (-(b m)))‖
        ≤ ‖iteratedFDeriv ℝ (i - j) g (seeleyLam (X := E) (-(b m)) x)‖ * (b m) ^ (i - j) := by
          refine (norm_compContinuousLinearMap_const_le _ (-(b m))).trans_eq ?_
          rw [show max 1 |(-(b m))| = b m from by
            rw [abs_neg, abs_of_nonneg hbm0.le]; exact max_eq_right hbm1]
      _ ≤ R * (b m) ^ (i - j) := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hbm0.le _)
          exact hR (seeleyLam (X := E) (-(b m)) x) (hsubs ⟨x, hxs, rfl⟩) (i - j) (Nat.sub_le i j)
  calc ∑ j ∈ Finset.range (i + 1),
        (i.choose j : ℝ) * ‖iteratedFDerivWithin ℝ j f₁ s x‖
          * ‖iteratedFDerivWithin ℝ (i - j) f₂ s x‖
      ≤ ∑ j ∈ Finset.range (i + 1),
          (i.choose j : ℝ) * (|a m| * (seeleyCutB j * (b m) ^ j)) * (R * (b m) ^ (i - j)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        exact mul_le_mul (mul_le_mul le_rfl (hbound1 j hj) (norm_nonneg _) (Nat.cast_nonneg _))
          (hbound2 j hj) (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (abs_nonneg _)
            (mul_nonneg (seeleyCutB_nonneg j) (pow_nonneg hbm0.le j))))
    _ = ∑ j ∈ Finset.range (i + 1),
          |a m| * (b m) ^ i * (R * ((i.choose j : ℝ) * seeleyCutB j)) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
        have hpow : (b m) ^ j * (b m) ^ (i - j) = (b m) ^ i := by
          rw [← pow_add, Nat.add_sub_cancel' hji]
        calc (i.choose j : ℝ) * (|a m| * (seeleyCutB j * (b m) ^ j)) * (R * (b m) ^ (i - j))
            = |a m| * R * ((i.choose j : ℝ) * seeleyCutB j)
                * ((b m) ^ j * (b m) ^ (i - j)) := by ring
          _ = |a m| * R * ((i.choose j : ℝ) * seeleyCutB j) * (b m) ^ i := by rw [hpow]
          _ = |a m| * (b m) ^ i * (R * ((i.choose j : ℝ) * seeleyCutB j)) := by ring
    _ = |a m| * (b m) ^ i * ((∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j) * R) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-! ## Auxiliary series lemmas -/

/-- Comparison of the two kinds of truncated tails. -/
lemma tsum_indicator_le_of_le {b c : ℕ → ℝ} {N : ℕ} {t : ℝ} (h : ∀ m ≥ N, t ≤ b m)
    (hc : Summable c) (hc0 : ∀ m, 0 ≤ c m) :
    (∑' m, if N ≤ m then c m else 0) ≤ ∑' m, if t ≤ b m then c m else 0 := by
  have h1 : Summable fun m : ℕ => if N ≤ m then c m else 0 := by
    refine Summable.of_norm_bounded hc fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases hm : N ≤ m
    · rw [ite_eq_left hm, abs_of_nonneg (hc0 m)]
    · rw [ite_eq_right hm, abs_zero]
      exact hc0 m
  have h2 : Summable fun m : ℕ => if t ≤ b m then c m else 0 := by
    refine Summable.of_norm_bounded hc fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases hm : t ≤ b m
    · rw [ite_eq_left hm, abs_of_nonneg (hc0 m)]
    · rw [ite_eq_right hm, abs_zero]
      exact hc0 m
  refine Summable.tsum_le_tsum (fun m => ?_) h1 h2
  by_cases hm : N ≤ m
  · rw [ite_eq_left hm, ite_eq_left (h m hm)]
  · rw [ite_eq_right hm]
    by_cases h2' : t ≤ b m
    · rw [ite_eq_left h2']
      exact hc0 m
    · rw [ite_eq_right h2']

/-- A finite sum of nonnegative reals is bounded by the full sum. -/
lemma finset_sum_le_tsum_of_nonneg {f : ℕ → ℝ} (hf : Summable f) (hf0 : ∀ m, 0 ≤ f m)
    (s : Finset ℕ) : ∑ m ∈ s, f m ≤ ∑' m, f m := by
  have hs : Summable (fun m : ℕ => if m ∈ s then f m else 0) := by
    refine Summable.of_norm_bounded (g := f) hf fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases h : m ∈ s
    · rw [ite_eq_left h, abs_of_nonneg (hf0 m)]
    · rw [ite_eq_right h, abs_zero]
      exact hf0 m
  have h1 : ∑ m ∈ s, f m = ∑' m, (if m ∈ s then f m else 0) := by
    rw [tsum_eq_sum (s := s) (f := fun m : ℕ => if m ∈ s then f m else 0)
      (fun m hm => by rw [ite_eq_right (by simpa using hm)])]
    exact Finset.sum_congr rfl fun m hm => by rw [ite_eq_left (by simpa using hm)]
  rw [h1]
  refine Summable.tsum_le_tsum (fun m => ?_) hs hf
  by_cases h : m ∈ s
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact hf0 m

/-- Splitting off a finite sum from a `tsum`. -/
lemma tsum_sub_finset_sum_eq {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [T2Space M] {f : ℕ → M} (hf : Summable f) (A : Finset ℕ) :
    (∑' m, f m) - ∑ m ∈ A, f m = ∑' m, (if m ∈ A then 0 else f m) := by
  have hsum : Summable (fun m : ℕ => if m ∈ A then f m else 0) :=
    summable_of_ne_finset_zero (s := A) (fun m hm => by rw [ite_eq_right (by simpa using hm)])
  have hval : (∑' m, (if m ∈ A then f m else 0)) = ∑ m ∈ A, f m := by
    rw [tsum_eq_sum (s := A) (f := fun m : ℕ => if m ∈ A then f m else 0)
      (fun m hm => by rw [ite_eq_right (by simpa using hm)])]
    exact Finset.sum_congr rfl fun m hm => by rw [ite_eq_left (by simpa using hm)]
  have hA : HasSum (fun m : ℕ => if m ∈ A then f m else 0) (∑ m ∈ A, f m) := by
    rw [← hval]; exact hsum.hasSum
  have hsub := hf.hasSum.sub hA
  have heq : (fun m => f m - (if m ∈ A then f m else 0))
      = (fun m => if m ∈ A then 0 else f m) := by
    funext m
    by_cases h : m ∈ A <;> simp [h]
  rw [heq] at hsub
  exact hsub.tsum_eq.symm

/-- Bound for the norm of a series whose terms are dominated by a multiple of a nonnegative
summable family. -/
lemma norm_tsum_le_mul_tsum {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    {v : ℕ → M} {c : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hv : Summable fun m => ‖v m‖) (hc0 : ∀ m, 0 ≤ c m) (hc : Summable c)
    (h : ∀ m, ‖v m‖ ≤ C * c m) :
    ‖∑' m, v m‖ ≤ C * ∑' m, c m := by
  have hcs : Summable fun m => C * c m := hc.mul_left C
  calc ‖∑' m, v m‖ ≤ ∑' m, ‖v m‖ := norm_tsum_le_tsum_norm hv
    _ ≤ ∑' m, C * c m := Summable.tsum_le_tsum h hv hcs
    _ = C * ∑' m, c m := tsum_mul_left

/-! ## The finite-sum form of the jet identity -/

/-- On the open lower half space the iterated derivative of the Seeley extension is the finite sum
of the iterated derivatives of the Seeley terms, up to any truncation index for which the
remaining terms already vanish on a neighbourhood of the point. -/
lemma seeleyLoc_iteratedFDeriv_eq_sum_range {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop) {W : Set E} (hW : IsOpen W)
    {i : ℕ} {g : E × ℝ → ℂ} (hg : ContDiffOn ℝ (i : WithTop ENat) g (seHp W))
    {x : E × ℝ} (hx : x.1 ∈ W) (hx2 : x.2 < 0) {N : ℕ}
    (hN : ∀ m ≥ N, 4 ≤ b m * |x.2|) :
    iteratedFDeriv ℝ i (seeleyExt a b g) x
      = ∑ n ∈ Finset.range N, iteratedFDeriv ℝ i (seeleyTerm a b g n) x := by
  have hx' : x ∈ seLw W (|x.2| + 1) := by
    refine mem_seLw.mpr ⟨hx, ?_, hx2⟩
    rw [abs_of_neg hx2]; linarith
  rw [seeleyLoc_iteratedFDeriv_eq_tsum hb hbT hW hg hx' hN]
  refine tsum_eq_sum (s := Finset.range N) fun n hn => ?_
  have hnN : N ≤ n := by simpa [Finset.mem_range, not_lt] using hn
  have hneigh : {q : E × ℝ | q.2 < x.2 / 2} ∈ 𝓝 x :=
    (isOpen_lt continuous_snd continuous_const).mem_nhds (by show x.2 < x.2 / 2; linarith)
  have hz : seeleyTerm a b g n =ᶠ[𝓝 x] 0 := by
    filter_upwards [hneigh] with q hq
    exact seeleyLoc_seeleyTerm_eq_zero_of_abs (by linarith [hb n]) (hN n hnN) hx2 hq
  rw [seeleyLoc_iteratedFDeriv_congr_of_eventuallyEq hz i]
  simp

/-- Jet matching from below at the hyperplane: the iterated derivatives of the Seeley extension converge, as one approaches a boundary point inside the open lower half space, to the same limit to which the iterated derivatives of `g` converge from the open upper half space. -/
theorem seeleyJetMatchLower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j)
    {W : Set E} (hW : IsOpen W) {k : ℕ} {g : E × ℝ → ℂ}
    (hfin : Work.CR.Flat.holderNorm k α g (seUp W) ≠ ⊤)
    {i : ℕ} (hi : i ≤ k) (hg : ContDiffOn ℝ (i : WithTop ENat) g (seHp W))
    {p : E × ℝ} (hp : p ∈ seHp W) (hp0 : p.2 = 0)
    {L : ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ}
    (hL : Filter.Tendsto (fun q : E × ℝ => iteratedFDeriv ℝ i g q)
      (nhdsWithin p (seUp W)) (nhds L)) :
    Filter.Tendsto (fun q : E × ℝ => iteratedFDeriv ℝ i (seeleyExt a b g) q)
      (nhdsWithin p {q : E × ℝ | q.2 < 0}) (nhds L) := by
  classical
  have hb1 : ∀ m, (1 : ℝ) ≤ b m := fun m => by linarith [hb m]
  have hb0 : ∀ m, (0 : ℝ) < b m := fun m => lt_of_lt_of_le one_pos (hb1 m)
  have hpW : p.1 ∈ W := (mem_seHp.mp hp).1
  -- ## sup bound for the derivatives of `g` of order `≤ i` on the open upper half space
  set R : ℝ := (Work.CR.Flat.holderNorm k α g (seUp W)).toReal with hRdef
  have hR0 : 0 ≤ R := ENNReal.toReal_nonneg
  have hR : ∀ z ∈ seUp W, ∀ j ≤ i, ‖iteratedFDeriv ℝ j g z‖ ≤ R := by
    intro z hz j hj
    have h3 : ENNReal.ofReal R = Work.CR.Flat.holderNorm k α g (seUp W) := by
      rw [hRdef]; exact ENNReal.ofReal_toReal hfin
    have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ j g z‖ ≤ ENNReal.ofReal R := by
      rw [h3]
      have hle := Work.CR.Flat.le_iterDerivNorm j g (seUp W) hz
      rw [iteratedFDerivWithin_of_isOpen j (isOpen_seUp hW) hz] at hle
      exact le_trans hle
        (Work.CR.Flat.iterDerivNorm_le_holderNorm k α g (seUp W) (le_trans hj hi))
    exact (ENNReal.ofReal_le_ofReal_iff hR0).mp h1
  set K : ℝ := ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (seeleyCutB_nonneg j)
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- ## the constants and the tail threshold
  set Ct : ℝ := R + ‖L‖ + (‖L‖ + K * R) + 1 with hCtdef
  have hKR0 : 0 ≤ K * R := mul_nonneg hK0 hR0
  have hCt0 : 0 < Ct := by rw [hCtdef]; linarith [norm_nonneg L, hR0, hKR0]
  have hCtge : R + ‖L‖ + (‖L‖ + K * R) ≤ Ct := by rw [hCtdef]; linarith
  have hL0 : 0 ≤ ‖L‖ := norm_nonneg L
  have hC0 : 0 ≤ R + ‖L‖ := by linarith [hR0, hL0]
  have hCtR : R + ‖L‖ ≤ Ct := by linarith [hCtge, hL0, hKR0]
  have hCtL : ‖L‖ ≤ Ct := by linarith [hCtge, hR0, hKR0]
  have hCtKR : K * R ≤ Ct := by linarith [hCtge, hL0, hR0]
  set δ : ℝ := ε / (2 * Ct) with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hCtδ : Ct * δ = ε / 2 := by
    rw [hδdef]
    field_simp [hCt0.ne']
  have hc0 : ∀ m, 0 ≤ |a m| * (b m) ^ i := fun m =>
    mul_nonneg (abs_nonneg _) (pow_nonneg (hb0 m).le i)
  obtain ⟨t₀, ht₀⟩ := Work.NN.Seeley.exists_tsum_indicator_le hbT (hsum i) hc0 hδ0
  set t : ℝ := max t₀ 1 with htdef
  have htpos : 0 < t := lt_of_lt_of_le one_pos (le_max_right t₀ 1)
  have ht₀le : t₀ ≤ t := le_max_left t₀ 1
  set St : ℝ := ∑' m, if t ≤ b m then |a m| * (b m) ^ i else 0 with hStdef
  have hSt0 : 0 ≤ St := by
    rw [hStdef]
    exact tsum_nonneg fun m => by by_cases h : t ≤ b m <;> simp [h, hc0 m]
  have hStδ : St ≤ δ := by rw [hStdef]; exact ht₀ t ht₀le
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, ∀ m ≥ N0, t ≤ b m := exists_b_ge hbT t
  have hIdx : (∑' m, if N0 ≤ m then |a m| * (b m) ^ i else 0) ≤ St :=
    tsum_indicator_le_of_le hN0 (hsum i) hc0
  -- ## the finite part tends to `0`
  have hfin_ev : ∀ᶠ q in nhdsWithin p {q : E × ℝ | q.2 < 0},
      ∑ m ∈ Finset.range N0,
        |a m| * (b m) ^ i * ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖ < ε / 2 := by
    have hF : ∀ m : ℕ, Filter.Tendsto (fun q : E × ℝ =>
        |a m| * (b m) ^ i * ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖)
        (nhdsWithin p {q : E × ℝ | q.2 < 0}) (nhds 0) := by
      intro m
      have hWmem : {q : E × ℝ | q.1 ∈ W} ∈ nhdsWithin p {q : E × ℝ | q.2 < 0} :=
        nhdsWithin_le_nhds ((continuous_fst.tendsto p).eventually (hW.mem_nhds hpW))
      have hφ : Filter.Tendsto (fun q : E × ℝ => seeleyLam (X := E) (-(b m)) q)
          (nhdsWithin p {q : E × ℝ | q.2 < 0}) (nhdsWithin p (seUp W)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have hcont : Continuous fun q : E × ℝ => seeleyLam (X := E) (-(b m)) q := by fun_prop
          have hφp : seeleyLam (X := E) (-(b m)) p = p := by
            rw [seeleyLam_apply, hp0, mul_zero]
            exact Prod.ext rfl (by rw [hp0])
          have h := (hcont.tendsto p).mono_left (nhdsWithin_le_nhds (s := {q : E × ℝ | q.2 < 0}))
          rwa [hφp] at h
        · filter_upwards [self_mem_nhdsWithin, hWmem] with q hq2 hqW'
          refine mem_seUp.mpr ⟨hqW', ?_⟩
          rw [seeleyLam_apply]
          nlinarith [hb0 m]
      have h1 : Filter.Tendsto (fun q : E × ℝ =>
          ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖)
          (nhdsWithin p {q : E × ℝ | q.2 < 0}) (nhds 0) := by
        have h2 := (hL.comp hφ).sub (tendsto_const_nhds (x := L))
        simpa using h2.norm
      simpa using h1.const_mul (|a m| * (b m) ^ i)
    have hsumlim : Filter.Tendsto (fun q : E × ℝ => ∑ m ∈ Finset.range N0,
        |a m| * (b m) ^ i * ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖)
        (nhdsWithin p {q : E × ℝ | q.2 < 0}) (nhds 0) := by
      simpa using tendsto_finsetSum (Finset.range N0) (fun m _ => hF m)
    have hlt := hsumlim.eventually_lt tendsto_const_nhds (by linarith : (0 : ℝ) < ε / 2)
    simpa using hlt
  -- ## the neighbourhood
  have hqW' : ∀ᶠ q in nhdsWithin p {q : E × ℝ | q.2 < 0}, q.1 ∈ W :=
    nhdsWithin_le_nhds ((continuous_fst.tendsto p).eventually (hW.mem_nhds hpW))
  have hq2' : ∀ᶠ q in nhdsWithin p {q : E × ℝ | q.2 < 0}, q.2 < 0 := self_mem_nhdsWithin
  have hqdist : ∀ᶠ q in nhdsWithin p {q : E × ℝ | q.2 < 0}, |q.2| < 1 / t := by
    have hcont : Continuous fun q : E × ℝ => |q.2| := continuous_abs.comp continuous_snd
    have hlim : Filter.Tendsto (fun q : E × ℝ => |q.2|)
        (nhdsWithin p {q : E × ℝ | q.2 < 0}) (nhds 0) := by
      simpa [hp0] using (hcont.tendsto p).mono_left nhdsWithin_le_nhds
    exact hlim.eventually ((isOpen_lt continuous_id continuous_const).mem_nhds
      (one_div_pos.mpr htpos))
  filter_upwards [hqW', hq2', hqdist, hfin_ev] with q hqWq hq2q hqdistq hfinq
  rw [dist_eq_norm]
  -- ## the truncation index
  have hqabs : 0 < |q.2| := abs_pos.mpr (ne_of_lt hq2q)
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ m ≥ M, 4 ≤ b m * |q.2| := by
    obtain ⟨M, hM⟩ := exists_b_ge hbT (4 / |q.2|)
    exact ⟨M, fun m hm => by
      have h := hM m hm
      rw [div_le_iff₀ hqabs] at h
      exact h⟩
  have ht_lt : t < 1 / |q.2| := by
    have h := hqdistq
    rw [lt_div_iff₀ htpos] at h
    rw [lt_div_iff₀ hqabs]
    nlinarith [h]
  have hrepr : iteratedFDeriv ℝ i (seeleyExt a b g) q
      = ∑ n ∈ Finset.range M, iteratedFDeriv ℝ i (seeleyTerm a b g n) q :=
    seeleyLoc_iteratedFDeriv_eq_sum_range hb hbT hW hg hqWq hq2q hM
  set A : Finset ℕ := (Finset.range M).filter (fun m => b m * |q.2| < 1) with hAdef
  set B : Finset ℕ := (Finset.range M).filter (fun m => ¬ (b m * |q.2| < 1)) with hBdef
  have hsplit : ∑ m ∈ Finset.range M, iteratedFDeriv ℝ i (seeleyTerm a b g m) q
      = ∑ m ∈ A, iteratedFDeriv ℝ i (seeleyTerm a b g m) q
        + ∑ m ∈ B, iteratedFDeriv ℝ i (seeleyTerm a b g m) q := by
    rw [hAdef, hBdef, ← Finset.sum_filter_add_sum_filter_not (Finset.range M)
      (fun m => b m * |q.2| < 1) (fun m => iteratedFDeriv ℝ i (seeleyTerm a b g m) q)]
  have hMle : ∀ m ∉ A, t ≤ b m := by
    intro m hm
    have hge : 1 ≤ b m * |q.2| := by
      by_cases hmM : m < M
      · by_contra hlt
        have hmA : m ∈ A := by
          rw [hAdef]
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmM, lt_of_not_ge hlt⟩
        exact hm hmA
      · have h2 : 4 ≤ b m * |q.2| := hM m (le_of_not_gt hmM)
        linarith
    calc t ≤ 1 / |q.2| := le_of_lt ht_lt
      _ ≤ b m := by rw [div_le_iff₀ hqabs]; linarith
  -- ## the main/cutoff decomposition of the terms
  set Main : ℕ → ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ :=
    fun m => (iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q)).compContinuousLinearMap
      (fun _ => seeleyLam (X := E) (-(b m))) with hMaindef
  set Tl : ℕ → ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ :=
    fun m => L.compContinuousLinearMap (fun _ => seeleyLam (X := E) (-(b m))) with hTldef
  have hAterm : ∀ m ∈ A, iteratedFDeriv ℝ i (seeleyTerm a b g m) q = (a m) • Main m := by
    intro m hm
    rw [hMaindef]
    rw [hAdef] at hm
    obtain ⟨-, hmc⟩ := Finset.mem_filter.mp hm
    exact iteratedFDeriv_seeleyTerm_eq_comp_shear hW hb1 hg hqWq hq2q (by
      rw [abs_neg_mul, abs_of_nonneg (hb0 m).le]; exact hmc)
  have hdecomp : iteratedFDeriv ℝ i (seeleyExt a b g) q - L
      = (∑ m ∈ A, ((a m) • Main m - (a m) • Tl m)) + ((∑ m ∈ A, (a m) • Tl m) - L)
        + ∑ m ∈ B, iteratedFDeriv ℝ i (seeleyTerm a b g m) q := by
    rw [hrepr, hsplit, Finset.sum_congr rfl (fun m hm => hAterm m hm), Finset.sum_sub_distrib]
    abel
  -- ## the bound for the main part
  have he1 : ‖∑ m ∈ A, ((a m) • Main m - (a m) • Tl m)‖
      ≤ (∑ m ∈ Finset.range N0,
            |a m| * (b m) ^ i * ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖)
        + (R + ‖L‖) * St := by
    have hp : ∀ m, (a m) • Main m - (a m) • Tl m
        = (a m) • ((iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L).compContinuousLinearMap
            (fun _ => seeleyLam (X := E) (-(b m)))) := by
      intro m
      simp only [hMaindef, hTldef]
      exact (smul_sub (a m) _ _).symm.trans (by rw [compContinuousLinearMap_sub_const])
    have he1eq : ∑ m ∈ A, ((a m) • Main m - (a m) • Tl m)
        = ∑ m ∈ A, (a m) • ((iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L).compContinuousLinearMap
            (fun _ => seeleyLam (X := E) (-(b m)))) :=
      Finset.sum_congr rfl fun m _ => hp m
    rw [he1eq]
    have hstep1 : ‖∑ m ∈ A, (a m) • ((iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L).compContinuousLinearMap
            (fun _ => seeleyLam (X := E) (-(b m))))‖
        ≤ ∑ m ∈ A,
            |a m| * (b m) ^ i * ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖ := by
      refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m hm => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      have hcomp : ‖((iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L)).compContinuousLinearMap
            (fun _ => seeleyLam (X := E) (-(b m)))‖
          ≤ ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖ * (b m) ^ i := by
        refine (norm_compContinuousLinearMap_const_le _ (-(b m))).trans_eq ?_
        rw [show max 1 |(-(b m))| = b m from by
          rw [abs_neg, abs_of_nonneg (hb0 m).le]; exact max_eq_right (hb1 m)]
      calc |a m| * ‖((iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L)).compContinuousLinearMap
              (fun _ => seeleyLam (X := E) (-(b m)))‖
          ≤ |a m| * (‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖ * (b m) ^ i) :=
            mul_le_mul_of_nonneg_left hcomp (abs_nonneg _)
        _ = |a m| * (b m) ^ i * ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖ := by
            ring
    refine hstep1.trans ?_
    have hbig : ∀ m : ℕ,
        |a m| * (b m) ^ i * ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖
          ≤ |a m| * (b m) ^ i * (R + ‖L‖) := by
      intro m
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (abs_nonneg _) (pow_nonneg (hb0 m).le i))
      have hle : ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q)‖ ≤ R :=
        hR (seeleyLam (X := E) (-(b m)) q)
          (mem_seUp.mpr ⟨hqWq, by rw [seeleyLam_apply]; nlinarith [hb0 m]⟩) i le_rfl
      calc ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖
          ≤ ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q)‖ + ‖L‖ := norm_sub_le _ _
        _ ≤ R + ‖L‖ := by linarith
    have hsplitA : ∑ m ∈ A, |a m| * (b m) ^ i * ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖
        = ∑ m ∈ A.filter (fun m => m < N0),
              |a m| * (b m) ^ i * ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖
          + ∑ m ∈ A.filter (fun m => ¬ m < N0),
              |a m| * (b m) ^ i * ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖ := by
      rw [← Finset.sum_filter_add_sum_filter_not A (fun m => m < N0)
        (fun m => |a m| * (b m) ^ i * ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖)]
    rw [hsplitA]
    refine add_le_add ?_ ?_
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro m hm
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hm).2
      · intro m hm hmn
        exact mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (hb0 m).le i)) (norm_nonneg _)
    · have hs : ∑ m ∈ A.filter (fun m => ¬ m < N0), |a m| * (b m) ^ i ≤ St := by
        have hg : Summable (fun m : ℕ => if N0 ≤ m then |a m| * (b m) ^ i else 0) := by
          refine Summable.of_norm_bounded (hsum i) fun m => ?_
          rw [Real.norm_eq_abs]
          by_cases h : N0 ≤ m
          · rw [ite_eq_left h, abs_of_nonneg (hc0 m)]
          · rw [ite_eq_right h, abs_zero]; exact hc0 m
        have h2 : ∑ m ∈ A.filter (fun m => ¬ m < N0), |a m| * (b m) ^ i
            = ∑ m ∈ A.filter (fun m => ¬ m < N0), (if N0 ≤ m then |a m| * (b m) ^ i else 0) := by
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [ite_eq_left (le_of_not_gt (Finset.mem_filter.mp hm).2)]
        rw [h2]
        exact le_trans (finset_sum_le_tsum_of_nonneg hg
          (fun m => by by_cases h : N0 ≤ m <;> simp [h, hc0 m]) _) hIdx
      calc ∑ m ∈ A.filter (fun m => ¬ m < N0),
              |a m| * (b m) ^ i * ‖iteratedFDeriv ℝ i g (seeleyLam (X := E) (-(b m)) q) - L‖
          ≤ ∑ m ∈ A.filter (fun m => ¬ m < N0), |a m| * (b m) ^ i * (R + ‖L‖) :=
            Finset.sum_le_sum fun m hm => hbig m
        _ = (∑ m ∈ A.filter (fun m => ¬ m < N0), |a m| * (b m) ^ i) * (R + ‖L‖) := by
            rw [← Finset.sum_mul]
        _ ≤ St * (R + ‖L‖) := mul_le_mul_of_nonneg_right hs hC0
        _ = (R + ‖L‖) * St := by ring
  -- ## the bound for the difference with `L`
  have hTlbound : ∀ m : ℕ, ‖(a m) • Tl m‖ ≤ |a m| * (b m) ^ i * ‖L‖ := by
    intro m
    change ‖(a m) • (L.compContinuousLinearMap (fun _ => seeleyLam (X := E) (-(b m))))‖
      ≤ |a m| * (b m) ^ i * ‖L‖
    rw [norm_smul, Real.norm_eq_abs]
    calc |a m| * ‖L.compContinuousLinearMap (fun _ => seeleyLam (X := E) (-(b m)))‖
        ≤ |a m| * (‖L‖ * (b m) ^ i) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          refine (norm_compContinuousLinearMap_const_le _ (-(b m))).trans_eq ?_
          rw [show max 1 |(-(b m))| = b m from by
            rw [abs_neg, abs_of_nonneg (hb0 m).le]; exact max_eq_right (hb1 m)]
      _ = |a m| * (b m) ^ i * ‖L‖ := by ring
  have hTlsummable : Summable (fun m : ℕ => (a m) • Tl m) := by
    refine Summable.of_norm_bounded (g := fun m => |a m| * (b m) ^ i * ‖L‖)
      ((hsum i).mul_right ‖L‖) fun m => ?_
    exact hTlbound m
  have hmom : (∑' m, (a m) • Tl m) = L := by
    rw [hTldef]
    exact Work.NN.Seeley.tsum_smul_compContinuousLinearMap_seeleyLam_eq hb1 ha hsum L
  have hcs : Summable (fun m : ℕ => if t ≤ b m then |a m| * (b m) ^ i else 0) := by
    refine Summable.of_norm_bounded (hsum i) fun m => ?_
    rw [Real.norm_eq_abs]
    by_cases h : t ≤ b m
    · rw [ite_eq_left h, abs_of_nonneg (hc0 m)]
    · rw [ite_eq_right h, abs_zero]; exact hc0 m
  have hcs0 : ∀ m, 0 ≤ (if t ≤ b m then |a m| * (b m) ^ i else 0) :=
    fun m => by by_cases h : t ≤ b m <;> simp [h, hc0 m]
  have he2 : ‖(∑ m ∈ A, (a m) • Tl m) - L‖ ≤ ‖L‖ * St := by
    have hkey : (∑ m ∈ A, (a m) • Tl m) - L
        = - ∑' m, (if m ∈ A then 0 else (a m) • Tl m) := by
      have h1 := tsum_sub_finset_sum_eq hTlsummable A
      rw [hmom] at h1
      rw [← h1, neg_sub]
    rw [hkey, norm_neg]
    have hv : Summable (fun m : ℕ => ‖if m ∈ A then
        (0 : ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ) else (a m) • Tl m‖) := by
      refine Summable.of_norm_bounded (g := fun m => |a m| * (b m) ^ i * ‖L‖)
        ((hsum i).mul_right ‖L‖) fun m => ?_
      by_cases h : m ∈ A
      · rw [ite_eq_left h, Real.norm_eq_abs, norm_zero, abs_zero]
        exact mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (hb0 m).le i)) hL0
      · rw [ite_eq_right h, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hTlbound m
    have hbnd : ∀ m, ‖if m ∈ A then
        (0 : ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ) else (a m) • Tl m‖
        ≤ ‖L‖ * (if t ≤ b m then |a m| * (b m) ^ i else 0) := by
      intro m
      by_cases h : m ∈ A
      · rw [ite_eq_left h]
        have hz : ‖(0 : ContinuousMultilinearMap ℝ (fun _ : Fin i => E × ℝ) ℂ)‖ = 0 := norm_zero
        rw [hz]
        exact mul_nonneg hL0 (hcs0 m)
      · rw [ite_eq_right h]
        have hle : t ≤ b m := hMle m h
        rw [ite_eq_left hle]
        refine le_trans (hTlbound m) ?_
        exact le_of_eq (by ring)
    refine le_trans (norm_tsum_le_mul_tsum hL0 hv hcs0 hcs hbnd) ?_
    rw [hStdef]
  -- ## the bound for the cutoff terms
  have hBsub : ∀ m ∈ B, m ∉ A := by
    intro m hm hA
    rw [hAdef] at hA
    rw [hBdef] at hm
    exact (Finset.mem_filter.mp hm).2 (Finset.mem_filter.mp hA).2
  have he3 : ‖∑ m ∈ B, iteratedFDeriv ℝ i (seeleyTerm a b g m) q‖ ≤ K * R * St := by
    have hterm : ∀ m ∈ B,
        ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) q‖ ≤ |a m| * (b m) ^ i * (K * R) := by
      intro m hm
      have h1 := norm_iteratedFDeriv_seeleyTerm_le (a := a) (b := b) (W := W) hW hb1 hg hR (m := m) (x := q) hqWq hq2q
      rwa [← hKdef] at h1
    have hs : ∑ m ∈ B, |a m| * (b m) ^ i ≤ St := by
      have h2 : ∑ m ∈ B, |a m| * (b m) ^ i
          = ∑ m ∈ B, (if t ≤ b m then |a m| * (b m) ^ i else 0) := by
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [ite_eq_left (hMle m (hBsub m hm))]
      rw [h2]
      exact le_trans (finset_sum_le_tsum_of_nonneg hcs hcs0 B) (le_of_eq hStdef.symm)
    calc ‖∑ m ∈ B, iteratedFDeriv ℝ i (seeleyTerm a b g m) q‖
        ≤ ∑ m ∈ B, ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) q‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ B, |a m| * (b m) ^ i * (K * R) := Finset.sum_le_sum hterm
      _ = (∑ m ∈ B, |a m| * (b m) ^ i) * (K * R) := by rw [← Finset.sum_mul]
      _ ≤ St * (K * R) := mul_le_mul_of_nonneg_right hs hKR0
      _ = K * R * St := by ring
  -- ## assembly
  have hsumtot : ‖∑ m ∈ A, ((a m) • Main m - (a m) • Tl m)‖
      + ‖(∑ m ∈ A, (a m) • Tl m) - L‖
      + ‖∑ m ∈ B, iteratedFDeriv ℝ i (seeleyTerm a b g m) q‖ < ε := by
    have h1 : (R + ‖L‖) * St ≤ (R + ‖L‖) * δ := mul_le_mul_of_nonneg_left hStδ hC0
    have h2 : ‖L‖ * St ≤ ‖L‖ * δ := mul_le_mul_of_nonneg_left hStδ hL0
    have h3 : K * R * St ≤ (K * R) * δ := mul_le_mul_of_nonneg_left hStδ hKR0
    have h4 : (R + ‖L‖) * δ + ‖L‖ * δ + (K * R) * δ ≤ ε / 2 := by
      have h4a : (R + ‖L‖) * δ + ‖L‖ * δ + (K * R) * δ
          = (R + ‖L‖ + (‖L‖ + K * R)) * δ := by ring
      rw [h4a]
      calc (R + ‖L‖ + (‖L‖ + K * R)) * δ ≤ Ct * δ := mul_le_mul_of_nonneg_right hCtge hδ0.le
        _ = ε / 2 := hCtδ
    linarith [he1, he2, he3, hfinq, h1, h2, h3, h4]
  calc ‖iteratedFDeriv ℝ i (seeleyExt a b g) q - L‖
      = ‖(∑ m ∈ A, ((a m) • Main m - (a m) • Tl m)) + ((∑ m ∈ A, (a m) • Tl m) - L)
          + ∑ m ∈ B, iteratedFDeriv ℝ i (seeleyTerm a b g m) q‖ := by rw [hdecomp]
    _ ≤ ‖∑ m ∈ A, ((a m) • Main m - (a m) • Tl m)‖
          + ‖(∑ m ∈ A, (a m) • Tl m) - L‖
          + ‖∑ m ∈ B, iteratedFDeriv ℝ i (seeleyTerm a b g m) q‖ := by
        have h1 := norm_add_le (∑ m ∈ A, ((a m) • Main m - (a m) • Tl m))
          ((∑ m ∈ A, (a m) • Tl m) - L)
        have h2 := norm_add_le ((∑ m ∈ A, ((a m) • Main m - (a m) • Tl m))
          + ((∑ m ∈ A, (a m) • Tl m) - L)) (∑ m ∈ B, iteratedFDeriv ℝ i (seeleyTerm a b g m) q)
        linarith
    _ < ε := hsumtot

end Work.NN.Final.JetMatch
