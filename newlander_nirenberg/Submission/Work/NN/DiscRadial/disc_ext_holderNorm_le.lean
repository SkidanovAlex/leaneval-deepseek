import Mathlib
import Submission.Work.NN.Final.DiscRadialDefs
import Submission.Work.NN.Final.HolderCongr
import Submission.Work.CR.Flat.Holder.holderNorm_mul_le
import Submission.Work.CR.Flat.Holder.holderNorm_smul
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.NN.DiscRadial.DiscRadialAux
import Submission.Work.NN.DiscRadial.holderNorm_radial_split
import Submission.Work.NN.DiscRadial.holderNorm_cutFun
import Submission.Work.NN.DiscRadial.cutFun_mul_reflMap_contDiffOn
import Submission.Work.NN.DiscRadial.holderNorm_comp_reflMap

noncomputable section
open scoped NNReal ENNReal ContDiff
open Set Metric

namespace Work.NN.DiscRadial
open Work.NN.Final Work.CR.Flat Work.CR.Flat.Holder

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]









/-! #### Elementary facts -/

lemma discExt_eq_discSum_of_one_lt {k : ℕ} {a b : ℕ → ℝ} {g : X × ℂ → ℂ} {p : X × ℂ}
    (hp : 1 < ‖p.2‖) : discExt k a b g p = discSum k a b g p := by
  unfold discExt
  rw [if_neg (by linarith : ¬ (‖p.2‖ < 1)),
      if_neg (by intro h; rw [h] at hp; linarith : ¬ (‖p.2‖ = 1))]

lemma setOf_neg_one_lt_norm_lt_eq_ball (r : ℝ) :
    {z : ℂ | (-1 : ℝ) < ‖z‖ ∧ ‖z‖ < r} = Metric.ball (0 : ℂ) r := by
  ext z
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨by linarith [norm_nonneg z], h⟩

theorem holderNorm_finset_sum_le {ι : Type*} (s : Finset ι) {k : ℕ} {α : ℝ}
    {g : ι → X → ℂ} {Ω : Set X}
    (hg : ∀ j ∈ s, ContDiffOn ℝ (k : WithTop ENat) (g j) Ω) (hΩ : UniqueDiffOn ℝ Ω) :
    Work.CR.Flat.holderNorm k α (fun x => ∑ j ∈ s, g j x) Ω
      ≤ ∑ j ∈ s, Work.CR.Flat.holderNorm k α (g j) Ω := by
  classical
  induction s using Finset.induction with
  | empty =>
      have h0 : (fun x => ∑ j ∈ (∅ : Finset ι), g j x) = (0 : X → ℂ) := by
        funext x; simp
      rw [h0, Work.CR.Flat.holderNorm_zero, Finset.sum_empty]
  | insert a t ha ih =>
      have ha' : ContDiffOn ℝ (k : WithTop ENat) (g a) Ω := hg a (Finset.mem_insert_self a t)
      have ht' : ∀ j ∈ t, ContDiffOn ℝ (k : WithTop ENat) (g j) Ω :=
        fun j hj => hg j (Finset.mem_insert_of_mem hj)
      have hsum : ContDiffOn ℝ (k : WithTop ENat) (fun x => ∑ j ∈ t, g j x) Ω :=
        ContDiffOn.sum fun j hj => ht' j hj
      have hcongr : (fun x => ∑ j ∈ insert a t, g j x) = g a + (fun x => ∑ j ∈ t, g j x) := by
        funext x; rw [Finset.sum_insert ha]; rfl
      rw [hcongr, Finset.sum_insert ha]
      exact (holderNorm_add_le ha' hsum hΩ).trans (add_le_add le_rfl (ih ht'))

/-! #### ENNReal arithmetic helpers -/

lemma ofReal_mul_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℝ≥0∞) :
    ENNReal.ofReal a * ENNReal.ofReal b * z = ENNReal.ofReal (a * b) * z := by
  rw [← ENNReal.ofReal_mul ha]

lemma ofReal_mul_mul' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (z : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * z) = ENNReal.ofReal (a * b) * z := by
  rw [← mul_assoc, ENNReal.ofReal_mul ha]

lemma ofReal_four_mul {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (z : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * (ENNReal.ofReal c * (ENNReal.ofReal d * z)))
      = ENNReal.ofReal (a * b * c * d) * z := by
  rw [ofReal_mul_mul' ha hb, ofReal_mul_mul' (mul_nonneg ha hb) hc,
      ofReal_mul_mul' (mul_nonneg (mul_nonneg ha hb) hc) hd]


section Main

theorem disc_ext_holderNorm_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {c : ℝ} (hc : 1 < c) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (U : Set X) (g : X × ℂ → ℂ), IsOpen U →
        (∀ m : ℕ, m ≤ k → ContDiffOn ℝ (m : WithTop ENat) g (U ×ˢ Metric.ball (0 : ℂ) 1)) →
        Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) 1) ≠ ⊤ →
        ContDiffOn ℝ (k : WithTop ENat)
          (Work.NN.Final.discExt k (Work.NN.Final.discWt k) Work.NN.Final.discScale g)
          (U ×ˢ Metric.ball (0 : ℂ) c) →
        Work.CR.Flat.holderNorm k α
            (Work.NN.Final.discExt k (Work.NN.Final.discWt k) Work.NN.Final.discScale g)
            (U ×ˢ Metric.ball (0 : ℂ) c)
          ≤ ENNReal.ofReal (C k) *
              Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) 1) := by
  have hαle : α ≤ 1 := le_of_lt hα1
  obtain ⟨K, hKpos, hKspec⟩ := holderNorm_radial_split (X := X) hα0
  have hb : ∀ m : ℕ, (2 : ℝ) ≤ discScale m := by
    intro m; rw [discScale]; push_cast; linarith
  choose Cc hCc using fun m : ℕ => holderNorm_comp_reflMap (X := X) hα0 hαle (discScale m) (hb m)
  choose Dd hDd using fun m : ℕ => holderNorm_cutFun (X := X) hα0 hαle (discScale m) (hb m)
  have hKpos' : ∀ k, 0 < max (K k) 1 := fun k => lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKspec' : ∀ (k : ℕ) (U : Set X) (a ρ d : ℝ), IsOpen U → a < ρ → ρ < d →
      ∀ f : X × ℂ → ℂ, ContDiffOn ℝ (k : WithTop ENat) f (U ×ˢ {z : ℂ | a < ‖z‖ ∧ ‖z‖ < d}) →
      holderNorm k α f (U ×ˢ {z : ℂ | a < ‖z‖ ∧ ‖z‖ < d})
        ≤ ENNReal.ofReal (max (K k) 1) * (holderNorm k α f (U ×ˢ {z : ℂ | a < ‖z‖ ∧ ‖z‖ < ρ})
            + holderNorm k α f (U ×ˢ {z : ℂ | ρ < ‖z‖ ∧ ‖z‖ < d})) := by
    intro k U a ρ d hU ha hd f hf
    refine (hKspec k U a ρ d hU ha hd f hf).trans ?_
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_max_left _ _)) _
  refine ⟨fun k => max (K k) 1 * (1 + ∑ m ∈ Finset.range (k + 1),
      max (K k) 1 * (|discWt k m| * (((k : ℝ) + 1) * 2 ^ (k + 1) * Dd m k * Cc m k))), ?_, ?_⟩
  · intro k
    have hKk : 0 < max (K k) 1 := hKpos' k
    have hCc0 : ∀ m, 0 < Cc m k := fun m => (hCc m).1 k
    have hDd0 : ∀ m, 0 < Dd m k := fun m => (hDd m).1 k
    have hsum : 0 ≤ ∑ m ∈ Finset.range (k + 1),
        max (K k) 1 * (|discWt k m| * (((k : ℝ) + 1) * 2 ^ (k + 1) * Dd m k * Cc m k)) := by
      refine Finset.sum_nonneg fun m _ => ?_
      have h1 : (0 : ℝ) ≤ |discWt k m| := abs_nonneg _
      have h2 : (0 : ℝ) ≤ ((k : ℝ) + 1) := by positivity
      have h3 : (0 : ℝ) ≤ 2 ^ (k + 1) := by positivity
      have h4 : (0 : ℝ) < Cc m k := hCc0 m
      have h5 : (0 : ℝ) < Dd m k := hDd0 m
      positivity
    exact mul_pos hKk (by linarith)
  · intro k U g hU hgsm hgfin hExt
    set ext : X × ℂ → ℂ := discExt k (discWt k) discScale g with hextdef
    set Ω : Set (X × ℂ) := U ×ˢ Metric.ball (0 : ℂ) c with hΩdef
    set Ω1 : Set (X × ℂ) := U ×ˢ Metric.ball (0 : ℂ) 1 with hΩ1def
    set Ω2 : Set (X × ℂ) := U ×ˢ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < c} with hΩ2def
    have hΩopen : IsOpen Ω := by rw [hΩdef]; exact hU.prod Metric.isOpen_ball
    have hΩ1open : IsOpen Ω1 := by rw [hΩ1def]; exact hU.prod Metric.isOpen_ball
    have hΩ2open : IsOpen Ω2 := by
      rw [hΩ2def]
      exact hU.prod ((isOpen_lt continuous_const continuous_norm).inter
        (isOpen_lt continuous_norm continuous_const))
    have hExtΩ : ContDiffOn ℝ (k : WithTop ENat) ext Ω := by rw [hextdef, hΩdef]; exact hExt
    have hgk : ContDiffOn ℝ (k : WithTop ENat) g Ω1 := hgsm k le_rfl
    have hstep1 : holderNorm k α ext Ω
        ≤ ENNReal.ofReal (max (K k) 1) * (holderNorm k α ext Ω1 + holderNorm k α ext Ω2) := by
      have hExtΩ' : ContDiffOn ℝ (k : WithTop ENat) ext
          (U ×ˢ {z : ℂ | -1 < ‖z‖ ∧ ‖z‖ < c}) := by
        rw [setOf_neg_one_lt_norm_lt_eq_ball c, ← hΩdef]
        exact hExtΩ
      have h := hKspec' k U (-1) 1 c hU (by norm_num) hc ext hExtΩ'
      rw [setOf_neg_one_lt_norm_lt_eq_ball c, setOf_neg_one_lt_norm_lt_eq_ball 1] at h
      simpa only [hΩdef, hΩ1def, hΩ2def] using h
    have hstep2 : holderNorm k α ext Ω1 = holderNorm k α g Ω1 := by
      refine holderNorm_congr_of_isOpen hΩ1open (fun p hp => ?_) k α
      have hp' : p ∈ U ×ˢ Metric.ball (0 : ℂ) 1 := hΩ1def ▸ hp
      obtain ⟨-, hpz⟩ := hp'
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hpz
      rw [hextdef]
      exact discExt_of_norm_lt_one hpz
    have hstep3 : holderNorm k α ext Ω2
        = holderNorm k α (discSum k (discWt k) discScale g) Ω2 := by
      refine holderNorm_congr_of_isOpen hΩ2open (fun p hp => ?_) k α
      have hp' : p ∈ U ×ˢ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < c} := hΩ2def ▸ hp
      rw [hextdef]
      exact discExt_eq_discSum_of_one_lt hp'.2.1
    have hkey : ∀ (m : ℕ), ∀ p ∈ Ω2,
        cutFun (discScale m) p * g (reflMap (discScale m) p)
          = cutFun (discScale m) p * ext (reflMap (discScale m) p) := by
      intro m p hp
      have hpz : 1 < ‖p.2‖ ∧ ‖p.2‖ < c := (hΩ2def ▸ hp).2
      by_cases h0 : cutFun (discScale m) p = 0
      · rw [h0, zero_mul, zero_mul]
      · have hlt : ‖(reflMap (discScale m) p).2‖ < 1 := by
          show ‖discRefl (discScale m) p.2‖ < 1
          have hsc : seeleyCut (discScale m * (‖p.2‖ - 1)) ≠ 0 := by
            intro hh; exact h0 (by rw [cutFun, hh]; simp)
          have habs : |discScale m * (‖p.2‖ - 1)| < 2 := by
            by_contra hc2
            exact hsc (seeleyCut_eq_zero (not_lt.mp hc2))
          have hx0 : (0 : ℝ) < discScale m * (‖p.2‖ - 1) :=
            mul_pos (discScale_pos m) (by linarith [hpz.1])
          have hlt2 : discScale m * (‖p.2‖ - 1) < 2 := by
            rw [← abs_of_pos hx0]; exact habs
          have hz0 : p.2 ≠ 0 := by
            intro hh; rw [hh] at hpz; simp at hpz; linarith [hpz.1]
          rw [norm_discRefl _ hz0, abs_lt]
          constructor <;> linarith
        rw [hextdef, discExt_of_norm_lt_one hlt]
    have hsm : ∀ m : ℕ, ContDiffOn ℝ (k : WithTop ENat)
        (discTerm (discWt k) discScale g m) Ω2 := by
      intro m
      have hQ5 := cutFun_mul_reflMap_contDiffOn (X := X) (U := U) (c := c)
        (b := discScale m) (k := k) (hb m) hc (w := ext) hExtΩ
      have hQ5' : ContDiffOn ℝ (k : WithTop ENat)
          (fun p : X × ℂ => cutFun (discScale m) p * ext (reflMap (discScale m) p)) Ω2 := by
        simpa only [hΩ2def] using hQ5
      have h1 : ContDiffOn ℝ (k : WithTop ENat)
          (fun p : X × ℂ => (discWt k m : ℝ) •
            (cutFun (discScale m) p * ext (reflMap (discScale m) p))) Ω2 :=
        ContDiffOn.const_smul _ hQ5'
      refine ContDiffOn.congr h1 (fun p hp => ?_)
      show discTerm (discWt k) discScale g m p
        = (discWt k m : ℝ) • (cutFun (discScale m) p * ext (reflMap (discScale m) p))
      rw [discTerm_eq, hkey m p hp, Complex.real_smul]
    have hstep4 : holderNorm k α (discSum k (discWt k) discScale g) Ω2
        ≤ ∑ m ∈ Finset.range (k + 1),
            holderNorm k α (discTerm (discWt k) discScale g m) Ω2 := by
      have hfun : discSum k (discWt k) discScale g
          = fun p => ∑ m ∈ Finset.range (k + 1), discTerm (discWt k) discScale g m p := rfl
      rw [hfun]
      exact holderNorm_finset_sum_le _ (fun m _ => hsm m) hΩ2open.uniqueDiffOn
    have hterm : ∀ m ∈ Finset.range (k + 1),
        holderNorm k α (discTerm (discWt k) discScale g m) Ω2
          ≤ ENNReal.ofReal (max (K k) 1 * (|discWt k m|
                * (((k : ℝ) + 1) * 2 ^ (k + 1) * Dd m k * Cc m k))) * holderNorm k α g Ω1 := by
      intro m hm
      set b : ℝ := discScale m with hbdef
      have hb2 : (2 : ℝ) ≤ b := by rw [hbdef]; exact hb m
      have hbpos' : (0 : ℝ) < b := by rw [hbdef]; exact discScale_pos m
      set A : Set (X × ℂ) := U ×ˢ annR b with hAdef
      have hAnnOpen : IsOpen (annR b) := by
        have h1 : annR b = {z : ℂ | 1 < ‖z‖} ∩ {z : ℂ | ‖z‖ < 1 + 2 / b} := by
          ext z; simp [annR]
        rw [h1]
        exact (isOpen_lt continuous_const continuous_norm).inter
          (isOpen_lt continuous_norm continuous_const)
      have hAopen : IsOpen A := by rw [hAdef]; exact hU.prod hAnnOpen
      set Tt : X × ℂ → ℂ := fun p => (discWt k m : ℂ) * (cutFun b p * ext (reflMap b p))
        with hTtdef
      have hTt_sm : ContDiffOn ℝ (k : WithTop ENat) Tt Ω2 := by
        have hQ5 := cutFun_mul_reflMap_contDiffOn (X := X) (U := U) (c := c) (b := b) (k := k)
          hb2 hc (w := ext) hExtΩ
        have hQ5' : ContDiffOn ℝ (k : WithTop ENat)
            (fun p : X × ℂ => cutFun b p * ext (reflMap b p)) Ω2 := by
          simpa only [hΩ2def] using hQ5
        have h1 : ContDiffOn ℝ (k : WithTop ENat)
            (fun p : X × ℂ => (discWt k m : ℝ) • (cutFun b p * ext (reflMap b p))) Ω2 :=
          ContDiffOn.const_smul _ hQ5'
        refine ContDiffOn.congr h1 (fun p hp => ?_)
        simp only [Pi.smul_apply, Complex.real_smul, hTtdef]
      have hTm_eq : ∀ p ∈ Ω2, discTerm (discWt k) discScale g m p = Tt p := by
        intro p hp
        show discTerm (discWt k) discScale g m p
          = (discWt k m : ℂ) * (cutFun b p * ext (reflMap b p))
        rw [hbdef, discTerm_eq]
        congr 1
        exact hkey m p hp
      have hcongr1 : holderNorm k α (discTerm (discWt k) discScale g m) Ω2
          = holderNorm k α Tt Ω2 :=
        holderNorm_congr_of_isOpen hΩ2open hTm_eq k α
      have hOut0 : holderNorm k α Tt (U ×ˢ {z : ℂ | 1 + 2 / b < ‖z‖ ∧ ‖z‖ < c}) = 0 := by
        have hzero : ∀ p ∈ (U ×ˢ {z : ℂ | 1 + 2 / b < ‖z‖ ∧ ‖z‖ < c}),
            Tt p = (0 : X × ℂ → ℂ) p := by
          intro p hp
          have hpz : 1 + 2 / b < ‖p.2‖ ∧ ‖p.2‖ < c := hp.2
          have hcut : cutFun b p = 0 := by
            have h2 : (2 : ℝ) < b * (‖p.2‖ - 1) := by
              have h3 : (1 + 2 / b) * b < ‖p.2‖ * b := mul_lt_mul_of_pos_right hpz.1 hbpos'
              have h4 : (1 + 2 / b) * b = b + 2 := by field_simp
              rw [h4] at h3
              nlinarith
            have harg : (2 : ℝ) ≤ |b * (‖p.2‖ - 1)| := by
              rw [abs_of_pos (by linarith)]; linarith
            simp only [cutFun, seeleyCut_eq_zero harg, Complex.ofReal_zero]
          simp only [hTtdef, Pi.zero_apply, hcut, zero_mul, mul_zero]
        rw [holderNorm_congr_of_isOpen (hU.prod ((isOpen_lt continuous_const
              continuous_norm).inter (isOpen_lt continuous_norm continuous_const))) hzero k α,
            Work.CR.Flat.holderNorm_zero]
      have hA_sub : Set.MapsTo (reflMap b) A (U ×ˢ Metric.ball (0 : ℂ) 1) := by
        intro p hp
        have hp' : p ∈ U ×ˢ annR b := hAdef ▸ hp
        refine ⟨hp'.1, ?_⟩
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact norm_reflMap_snd_lt_one hbpos' hp'.2
      have hcutC : ContDiffOn ℝ (k : WithTop ENat) (cutFun b) A := by
        have hnorm : ContDiffOn ℝ (k : WithTop ENat) (fun p : X × ℂ => ‖p.2‖) A := by
          have h1 : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun z : ℂ => ‖z‖) {z : ℂ | z ≠ 0} :=
            fun z hz => (contDiffAt_norm ℝ hz).contDiffWithinAt
          have h2 : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun p : X × ℂ => p.2) A :=
            (ContinuousLinearMap.snd ℝ X ℂ).contDiff.contDiffOn
          exact (h1.comp h2 (fun p hp => by
            have hp' : p ∈ U ×ˢ annR b := hAdef ▸ hp
            exact norm_ne_zero_iff.mp (ne_of_gt (by linarith [hp'.2.1] : (0:ℝ) < ‖p.2‖)))).of_le le_top
        have h3 : ContDiffOn ℝ (k : WithTop ENat) (fun p : X × ℂ => b * (‖p.2‖ - 1)) A :=
          contDiffOn_const.mul (hnorm.sub contDiffOn_const)
        have h4 : ContDiffOn ℝ (k : WithTop ENat)
            (fun p : X × ℂ => seeleyCut (b * (‖p.2‖ - 1))) A :=
          have hsmooth : ContDiffOn ℝ (k : WithTop ENat) seeleyCut (Set.univ : Set ℝ) :=
            (seeleyCut_contDiff.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn
          ContDiffOn.comp hsmooth h3 (fun p _ => Set.mem_univ _)
        have h5 : ContDiffOn ℝ (k : WithTop ENat)
            (fun p : X × ℂ => ((seeleyCut (b * (‖p.2‖ - 1)) : ℝ) : ℂ)) A :=
          Complex.ofRealCLM.contDiff.comp_contDiffOn h4
        exact h5
      have hcompC : ContDiffOn ℝ (k : WithTop ENat) (fun p => g (reflMap b p)) A := by
        have hΦ : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (reflMap b) A := by
          have hfst : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun p : X × ℂ => p.1) A :=
            (ContinuousLinearMap.fst ℝ X ℂ).contDiff.contDiffOn
          have hsnd : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun p : X × ℂ => discRefl b p.2) A := by
            have h1 : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun z : ℂ => discRefl b z)
                {z : ℂ | z ≠ 0} := contDiffOn_discRefl b
            have h2 : ContDiffOn ℝ (⊤ : WithTop ℕ∞) (fun p : X × ℂ => p.2) A :=
              (ContinuousLinearMap.snd ℝ X ℂ).contDiff.contDiffOn
            exact h1.comp h2 (fun p hp => by
              have hp' : p ∈ U ×ˢ annR b := hAdef ▸ hp
              exact norm_ne_zero_iff.mp (ne_of_gt (by linarith [hp'.2.1] : (0:ℝ) < ‖p.2‖)))
          exact hfst.prodMk hsnd
        exact hgk.comp (hΦ.of_le le_top) hA_sub
      have hcutA : holderNorm k α (cutFun b) A ≤ ENNReal.ofReal (Dd m k) := by
        have hle := (hDd m).2 k U hU
        simpa only [hbdef, hAdef, annR] using hle
      have hcutne : holderNorm k α (cutFun b) A ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcutA
      have hcompA : holderNorm k α (fun p => g (reflMap b p)) A
          ≤ ENNReal.ofReal (Cc m k) * holderNorm k α g Ω1 := by
        have hle := (hCc m).2 k U hU g hgsm
        simpa only [hbdef, hAdef, annR, hΩ1def] using hle
      have hcompne : holderNorm k α (fun p => g (reflMap b p)) A ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgfin) hcompA
      have hprod : holderNorm k α (fun p => cutFun b p * g (reflMap b p)) A
          ≤ ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * holderNorm k α (cutFun b) A
              * holderNorm k α (fun p => g (reflMap b p)) A :=
        holderNorm_mul_le hcutC hcompC hAopen.uniqueDiffOn hcutne hcompne
      have hprodC : ContDiffOn ℝ (k : WithTop ENat)
          (fun p => cutFun b p * g (reflMap b p)) A := hcutC.mul hcompC
      have hA_bound : holderNorm k α Tt A
          ≤ ENNReal.ofReal (|discWt k m|)
              * holderNorm k α (fun p => cutFun b p * g (reflMap b p)) A := by
        have heq : ∀ p ∈ A, Tt p = (discWt k m : ℂ) • (cutFun b p * g (reflMap b p)) := by
          intro p hp
          have hp' : p ∈ U ×ˢ annR b := hAdef ▸ hp
          have hlt : ‖(reflMap b p).2‖ < 1 := norm_reflMap_snd_lt_one hbpos' hp'.2
          rw [hTtdef]
          show (discWt k m : ℂ) * (cutFun b p * ext (reflMap b p))
            = (discWt k m : ℂ) • (cutFun b p * g (reflMap b p))
          rw [hextdef, discExt_of_norm_lt_one hlt, smul_eq_mul]
        have hsmul : holderNorm k α
            (fun x : X × ℂ => (discWt k m : ℂ) • (cutFun b x * g (reflMap b x))) A
            = ENNReal.ofReal |discWt k m|
                * holderNorm k α (fun p => cutFun b p * g (reflMap b p)) A := by
          rw [show (fun x : X × ℂ => (discWt k m : ℂ) • (cutFun b x * g (reflMap b x)))
                = (discWt k m : ℂ) • (fun p => cutFun b p * g (reflMap b p)) from rfl,
            holderNorm_smul (discWt k m : ℂ) hprodC hAopen.uniqueDiffOn]
          simp only [Complex.norm_real, Real.norm_eq_abs]
        rw [holderNorm_congr_of_isOpen hAopen heq k α, hsmul]
      have hglue : holderNorm k α Tt Ω2
          ≤ ENNReal.ofReal (max (K k) 1) * holderNorm k α Tt A := by
        by_cases hsplit : 1 + 2 / b < c
        · have h1b : (1 : ℝ) < 1 + 2 / b := by
            have : (0 : ℝ) < 2 / b := div_pos (by norm_num) hbpos'
            linarith
          have hTtΩ2 : ContDiffOn ℝ (k : WithTop ENat) Tt Ω2 := hTt_sm
          have h := hKspec' k U 1 (1 + 2 / b) c hU h1b hsplit Tt (by
            rw [← hΩ2def]; exact hTtΩ2)
          rw [hOut0, add_zero] at h
          simpa only [hΩ2def, hAdef, annR] using h
        · have hsub : Ω2 ⊆ A := by
            intro p hp
            have hp' : p ∈ U ×ˢ {z : ℂ | 1 < ‖z‖ ∧ ‖z‖ < c} := hΩ2def ▸ hp
            have hmem : p ∈ U ×ˢ annR b := by
              refine ⟨hp'.1, hp'.2.1, ?_⟩
              by_contra hcon
              push_neg at hcon
              linarith [not_lt.mp hsplit, hp'.2.2]
            simpa only [hAdef] using hmem
          have hmono : holderNorm k α Tt Ω2 ≤ holderNorm k α Tt A :=
            holderNorm_mono_set hAopen hΩ2open hsub k α Tt
          have hK1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (max (K k) 1) := by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
          calc holderNorm k α Tt Ω2 ≤ holderNorm k α Tt A := hmono
            _ = 1 * holderNorm k α Tt A := (one_mul (holderNorm k α Tt A)).symm
            _ ≤ ENNReal.ofReal (max (K k) 1) * holderNorm k α Tt A := mul_le_mul_left hK1 _
      have hQ : ((k : ℝ≥0∞) + 1) * 2 ^ (k + 1)
          = ENNReal.ofReal (((k : ℝ) + 1) * 2 ^ (k + 1)) := by
        have h1 : ((k : ℝ≥0∞) + 1) = ENNReal.ofReal ((k : ℝ) + 1) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_natCast k,
              ← ENNReal.ofReal_add (Nat.cast_nonneg k) zero_le_one]
        have h2 : (2 : ℝ≥0∞) ^ (k + 1) = ENNReal.ofReal ((2 : ℝ) ^ (k + 1)) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_pow (by norm_num)]
        rw [h1, h2, ← ENNReal.ofReal_mul (by positivity)]
      calc holderNorm k α (discTerm (discWt k) discScale g m) Ω2
          = holderNorm k α Tt Ω2 := hcongr1
        _ ≤ ENNReal.ofReal (max (K k) 1) * holderNorm k α Tt A := hglue
        _ ≤ ENNReal.ofReal (max (K k) 1) * (ENNReal.ofReal (|discWt k m|)
              * holderNorm k α (fun p => cutFun b p * g (reflMap b p)) A) :=
            mul_le_mul_right hA_bound _
        _ ≤ ENNReal.ofReal (max (K k) 1) * (ENNReal.ofReal (|discWt k m|)
              * (((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * holderNorm k α (cutFun b) A
                  * holderNorm k α (fun p => g (reflMap b p)) A)) :=
            mul_le_mul_right (mul_le_mul_right hprod _) _
        _ ≤ ENNReal.ofReal (max (K k) 1) * (ENNReal.ofReal (|discWt k m|)
              * (((k : ℝ≥0∞) + 1) * 2 ^ (k + 1) * ENNReal.ofReal (Dd m k)
                  * (ENNReal.ofReal (Cc m k) * holderNorm k α g Ω1))) := by
            refine mul_le_mul_right (mul_le_mul_right ?_ _) _
            exact mul_le_mul' (mul_le_mul' le_rfl hcutA) hcompA
        _ = ENNReal.ofReal (max (K k) 1 * (|discWt k m|
              * (((k : ℝ) + 1) * 2 ^ (k + 1) * Dd m k * Cc m k))) * holderNorm k α g Ω1 := by
            rw [hQ,
                show ENNReal.ofReal (((k : ℝ) + 1) * 2 ^ (k + 1)) * ENNReal.ofReal (Dd m k)
                  = ENNReal.ofReal ((((k : ℝ) + 1) * 2 ^ (k + 1)) * Dd m k)
                from (ENNReal.ofReal_mul (by positivity)).symm,
                ofReal_four_mul (le_of_lt (hKpos' k)) (abs_nonneg _)
                  (mul_nonneg (by positivity) (le_of_lt ((hDd m).1 k)))
                  (le_of_lt ((hCc m).1 k))]
            congr 1
            ring
    calc holderNorm k α ext Ω
        ≤ ENNReal.ofReal (max (K k) 1) * (holderNorm k α ext Ω1 + holderNorm k α ext Ω2) := hstep1
      _ = ENNReal.ofReal (max (K k) 1) * (holderNorm k α g Ω1
            + holderNorm k α (discSum k (discWt k) discScale g) Ω2) := by rw [hstep2, hstep3]
      _ ≤ ENNReal.ofReal (max (K k) 1) * (holderNorm k α g Ω1
            + ∑ m ∈ Finset.range (k + 1),
                holderNorm k α (discTerm (discWt k) discScale g m) Ω2) :=
          mul_le_mul_right (add_le_add le_rfl hstep4) _
      _ ≤ ENNReal.ofReal (max (K k) 1) * (holderNorm k α g Ω1
            + ∑ m ∈ Finset.range (k + 1),
                ENNReal.ofReal (max (K k) 1 * (|discWt k m|
                  * (((k : ℝ) + 1) * 2 ^ (k + 1) * Dd m k * Cc m k)))
                  * holderNorm k α g Ω1) :=
          mul_le_mul_right (add_le_add le_rfl (Finset.sum_le_sum hterm)) _
      _ = ENNReal.ofReal (max (K k) 1 * (1 + ∑ m ∈ Finset.range (k + 1),
              max (K k) 1 * (|discWt k m|
                * (((k : ℝ) + 1) * 2 ^ (k + 1) * Dd m k * Cc m k))))
              * holderNorm k α g Ω1 := by
            have hKk0 : (0 : ℝ) < max (K k) 1 := hKpos' k
            have hX0 : ∀ m : ℕ, (0 : ℝ) ≤ |discWt k m|
                * (((k : ℝ) + 1) * 2 ^ (k + 1) * Dd m k * Cc m k) := by
              intro m
              have h1 : (0 : ℝ) ≤ |discWt k m| := abs_nonneg _
              have h2 : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
              have h3 : (0 : ℝ) < 2 ^ (k + 1) := by positivity
              have h4 : (0 : ℝ) < Dd m k := (hDd m).1 k
              have h5 : (0 : ℝ) < Cc m k := (hCc m).1 k
              positivity
            have hY0 : (0 : ℝ) ≤ ∑ m ∈ Finset.range (k + 1),
                max (K k) 1 * (|discWt k m|
                  * (((k : ℝ) + 1) * 2 ^ (k + 1) * Dd m k * Cc m k)) :=
              Finset.sum_nonneg fun m _ => mul_nonneg hKk0.le (hX0 m)
            have hsum_eq : (∑ m ∈ Finset.range (k + 1),
                  ENNReal.ofReal (max (K k) 1 * (|discWt k m|
                    * (((k : ℝ) + 1) * 2 ^ (k + 1) * Dd m k * Cc m k)))
                  * holderNorm k α g Ω1)
                = ENNReal.ofReal (∑ m ∈ Finset.range (k + 1),
                    max (K k) 1 * (|discWt k m|
                      * (((k : ℝ) + 1) * 2 ^ (k + 1) * Dd m k * Cc m k)))
                  * holderNorm k α g Ω1 := by
              rw [← Finset.sum_mul]
              congr 1
              rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => mul_nonneg hKk0.le (hX0 m))]
            have e1 : ∀ a : ℝ≥0∞, holderNorm k α g Ω1 + a * holderNorm k α g Ω1
                = (1 + a) * holderNorm k α g Ω1 := fun a => by rw [add_mul, one_mul]
            rw [hsum_eq, e1, ← mul_assoc, ← ENNReal.ofReal_one,
                ← ENNReal.ofReal_add zero_le_one hY0, ← ENNReal.ofReal_mul hKk0.le]


end Main

end Work.NN.DiscRadial
