import Mathlib
import Submission.Work.Maximal.mstWide_defs
import Submission.Work.BourgainPlan.Maximal.mstProf_scale_decay
import Submission.Work.BourgainPlan.Maximal.mst_major_err1_l2
import Submission.Work.Maximal.mstEta_lipschitz
import Submission.Work.Maximal.mstBump_radius_lt_sep
import Submission.Work.Maximal.mstWideC_le_two_pow_kappa

namespace Work.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

noncomputable section

open Work.BourgainPlan.Maximal
open Work.BourgainPlan.IonescuWainger

/-! ## The level bump read at level `s+1` -/

/-- `𝒰(0) := ∅` only affects `s = 0`: for `s ≥ 1` the level set is `mstU l s`. -/
lemma mstLevel_eq_mstU_of_pos (l s : ℕ) (hs : 1 ≤ s) :
    mstLevel l s = mstU l s := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : s ≠ 0)
  exact mstLevel_succ l t

/-- The annulus `mstAnnulus l s` is the difference of the level-`(s+1)` and level-`s` arc sets
(needs `s ≥ 1` for the `𝒰(0) = ∅` convention). -/
lemma mstAnnulus_eq (l s : ℕ) (hs : 1 ≤ s) :
    mstAnnulus l s = mstU l (s + 1) \ mstU l s := by
  show mstLevel l (s + 1) \ mstLevel l s = mstU l (s + 1) \ mstU l s
  rw [mstLevel_succ l s, mstLevel_eq_mstU_of_pos l s hs]

/-- **At most one point of `𝒰(n)` in a ball of radius `e^{-n^{1/10}}`** (the points of `𝒰(n)` are
`2e^{-n^{1/10}}`-separated, `sigmaN_separated`). -/
lemma mstU_ball_unique (l : ℕ) (hl : 1 ≤ l) :
    ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∀ ξ : Circ,
      ∀ β ∈ mstU l n, ∀ β' ∈ mstU l n,
        ‖ξ - β‖ < Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) →
        ‖ξ - β'‖ < Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) → β = β' := by
  obtain ⟨Ns, hNs⟩ := sigmaN_separated (mstRho_pos l hl)
  refine ⟨max Ns 1, fun n hn ξ β hβ β' hβ' h1 h2 => ?_⟩
  by_contra hne
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have hNs' : Ns ≤ n ^ l := by
    have h1' : Ns ≤ n := le_trans (le_max_left _ _) hn
    calc Ns ≤ n := h1'
      _ = n ^ 1 := (pow_one n).symm
      _ ≤ n ^ l := Nat.pow_le_pow_right (by omega) hl
  have hβU : β ∈ sigmaLeFinset (taoSetS (mstRho l) (n ^ l)) (⌊2 / mstRho l⌋₊ + 1) := by
    simpa only [mstU, iwSigma, iwK] using hβ
  have hβU' : β' ∈ sigmaLeFinset (taoSetS (mstRho l) (n ^ l)) (⌊2 / mstRho l⌋₊ + 1) := by
    simpa only [mstU, iwSigma, iwK] using hβ'
  have hsep := hNs (n ^ l) hNs' β hβU β' hβU' hne
  rw [Nat.cast_pow, mstRho_pow_eq_real l hl n hn1] at hsep
  have htri : ‖β - β'‖ ≤ ‖β - ξ‖ + ‖ξ - β'‖ := by
    have h : β - β' = (β - ξ) + (ξ - β') := by abel
    rw [h]; exact norm_add_le _ _
  rw [norm_sub_rev β ξ] at htri
  linarith [hsep, htri, h1, h2]

/-! ## The pointwise estimate -/

/-- **The pointwise narrow-to-wide replacement of MST Theorem 8** (arXiv:1512.07518, the estimate
before eq. (149)): for every level `s` in the large-scale regime and every dyadic scale `k` with
`2^{κ_s} ≤ k`, the level-`s` model symbol `ν^s_{2^k} = mstNuS P l d χ η k s` (narrow bump
`mstEta d χ η s`) differs from the *wide* model `Ω^s_{2^k} = mstWideModel P l χ η k s` pointwise by at
most `C · (s+1)^{-δl} · 2^{-k/(2d)}`, uniformly in the circle point `ξ`. -/
theorem mstNuS_sub_mstWideModel_pointwise (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hc : 0 < P.leadingCoeff) (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0)
    {δ : ℝ} (hδ : 0 < δ) (D : ℝ) (hD : 0 < D)
    (hGauss : ∀ (s : ℕ) (β : Work.BourgainPlan.IonescuWainger.Circle),
      β ∈ Work.BourgainPlan.Maximal.mstU l (s + 1) \ Work.BourgainPlan.Maximal.mstU l s →
      ‖Work.BourgainPlan.Maximal.mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l))) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ k : ℕ,
      2 ^ (Work.BourgainPlan.Maximal.mstKappa P s) ≤ k →
      ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
      ‖Work.BourgainPlan.Maximal.mstNuS P l P.natDegree χ η k s ξ
          - Work.Maximal.mstWideModel P l χ η k s ξ‖
        ≤ C * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
            * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))) := by
  have hd1 : 1 ≤ P.natDegree := by omega
  have hd0 : (0 : ℝ) < (P.natDegree : ℝ) := by exact_mod_cast (by omega : 0 < P.natDegree)
  have hdR1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd1
  obtain ⟨L, hLpos, hL⟩ := mstEta_lipschitz η hηc hηsup
  obtain ⟨CΦ, hCΦpos, hCΦ⟩ := mstProf_scale_decay P hd
  obtain ⟨sR, hsR⟩ := mstBump_radius_lt_sep P hd hχ1
  obtain ⟨sB, hsB⟩ := mstWideC_le_two_pow_kappa P hd χ
  obtain ⟨sU, hsU⟩ := mstU_ball_unique l hl
  refine ⟨2 * L * CΦ + 1, by positivity, max (max sR sB) (max sU 1), ?_⟩
  intro s hs k hk ξ
  have hsRle : sR ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs
  have hsBle : sB ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs
  have hsUle : sU ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hs1 : 1 ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  have hr1 := (hsR s hsRle).1
  have hr2 := (hsR s hsRle).2
  have hAr := hsB s hsBle
  have hk1 : 1 ≤ k := le_trans Nat.one_le_two_pow hk
  have hη2 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0 := fun x hx => hηsup x (le_of_lt hx)
  -- support radii
  have hEta_supp : ∀ ζ : Circ, mstEta P.natDegree χ η s ζ ≠ 0 →
      ‖ζ‖ ≤ (1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ))) := by
    intro ζ hζ
    exact (mstEta_ne_zero_abs_iwRep_le_half (χ := χ) P.natDegree hd1 hχ1 η hη2 s hζ).2.2
  have hWide_supp : ∀ ζ : Circ, mstWideBump P χ η s ζ ≠ 0 →
      ‖ζ‖ ≤ 1 / (2 * mstWideC P s) := by
    intro ζ hζ
    by_contra hlt
    rw [not_le] at hlt
    exact hζ ((mstWideBump_memLp_and_narrow P χ η hηc.continuous hηsup s).2 ζ hlt)
  have hAeq : mstAnnulus l s = mstU l (s + 1) \ mstU l s := mstAnnulus_eq l s hs1
  have hmem : ∀ β : Circ, β ∈ mstAnnulus l s ↔ β ∈ mstU l (s + 1) ∧ β ∉ mstU l s := by
    intro β; rw [hAeq, Finset.mem_sdiff]
  -- the three filtered sets
  set T : Finset Circ := (mstAnnulus l s).filter
      (fun β => mstEta P.natDegree χ η s (ξ - β) ≠ 0) with hTdef
  set U : Finset Circ := (mstAnnulus l s).filter
      (fun β => mstWideBump P χ η s (ξ - β) ≠ 0) with hUdef
  set Z : Finset Circ := (mstAnnulus l s).filter
      (fun β => mstEta P.natDegree χ η s (ξ - β) - mstWideBump P χ η s (ξ - β) ≠ 0) with hZdef
  have hr1' : (1 / 2) * (2 : ℝ) ^ (-((s : ℝ) * ((P.natDegree : ℝ) - χ)))
      < Real.exp (-(((s + 1 : ℕ) : ℝ) ^ (1 / 10 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hr1
  have hr2' : 1 / (2 * mstWideC P s)
      < Real.exp (-(((s + 1 : ℕ) : ℝ) ^ (1 / 10 : ℝ))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hr2
  have hTcard : T.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [hTdef, Finset.mem_filter] at ha hb
    have ham : a ∈ mstU l (s + 1) := ((hmem a).mp ha.1).1
    have hbm : b ∈ mstU l (s + 1) := ((hmem b).mp hb.1).1
    have ha' : ‖ξ - a‖ < Real.exp (-(((s + 1 : ℕ) : ℝ) ^ (1 / 10 : ℝ))) :=
      lt_of_le_of_lt (hEta_supp (ξ - a) ha.2) hr1'
    have hb' : ‖ξ - b‖ < Real.exp (-(((s + 1 : ℕ) : ℝ) ^ (1 / 10 : ℝ))) :=
      lt_of_le_of_lt (hEta_supp (ξ - b) hb.2) hr1'
    exact hsU (s + 1) (by omega) ξ a ham b hbm ha' hb'
  have hUcard : U.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [hUdef, Finset.mem_filter] at ha hb
    have ham : a ∈ mstU l (s + 1) := ((hmem a).mp ha.1).1
    have hbm : b ∈ mstU l (s + 1) := ((hmem b).mp hb.1).1
    have ha' : ‖ξ - a‖ < Real.exp (-(((s + 1 : ℕ) : ℝ) ^ (1 / 10 : ℝ))) :=
      lt_of_le_of_lt (hWide_supp (ξ - a) ha.2) hr2'
    have hb' : ‖ξ - b‖ < Real.exp (-(((s + 1 : ℕ) : ℝ) ^ (1 / 10 : ℝ))) :=
      lt_of_le_of_lt (hWide_supp (ξ - b) hb.2) hr2'
    exact hsU (s + 1) (by omega) ξ a ham b hbm ha' hb'
  have hZ2 : Z.card ≤ 2 := by
    have hZU : Z ⊆ T ∪ U := by
      intro β hβ
      rw [hZdef, Finset.mem_filter] at hβ
      rcases eq_or_ne (mstEta P.natDegree χ η s (ξ - β)) 0 with he | he
      · refine Finset.mem_union.mpr (Or.inr ?_)
        refine Finset.mem_filter.mpr ⟨hβ.1, ?_⟩
        intro hw
        exact hβ.2 (by rw [he, hw, sub_zero])
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hβ.1, he⟩))
    calc Z.card ≤ (T ∪ U).card := Finset.card_le_card hZU
      _ ≤ T.card + U.card := Finset.card_union_le T U
      _ ≤ 2 := by omega
  -- the Lipschitz-type bound on the bump difference
  set R : ℝ := (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) + mstWideC P s with hRdef
  have hRnn : 0 ≤ R := by
    rw [hRdef]
    have := one_le_mstWideC P s
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) :=
      Real.rpow_nonneg (by norm_num) _
    linarith
  have hdiff : ∀ ζ : Circ,
      ‖mstEta P.natDegree χ η s ζ - mstWideBump P χ η s ζ‖ ≤ L * R * ‖ζ‖ := by
    intro ζ
    have hLb := hL ((2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) * iwRep ζ)
      (mstWideC P s * iwRep ζ)
    have heq : mstEta P.natDegree χ η s ζ - mstWideBump P χ η s ζ
        = η ((2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) * iwRep ζ)
            - η (mstWideC P s * iwRep ζ) := by
      rw [mstEta_apply, mstWideBump_apply]
    rw [heq]
    have habs : |(2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) * iwRep ζ
          - mstWideC P s * iwRep ζ|
        = |(2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) - mstWideC P s| * |iwRep ζ| := by
      rw [← sub_mul, abs_mul]
    have hle : |(2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) - mstWideC P s| ≤ R := by
      rw [hRdef, abs_sub_le_iff]
      have ha : (0 : ℝ) ≤ (2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) :=
        Real.rpow_nonneg (by norm_num) _
      have hb : (0 : ℝ) ≤ mstWideC P s := le_trans zero_le_one (one_le_mstWideC P s)
      constructor <;> linarith
    calc ‖η _ - η _‖ ≤ L * |(2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) * iwRep ζ
            - mstWideC P s * iwRep ζ| := hLb
      _ = L * (|(2 : ℝ) ^ ((s : ℝ) * ((P.natDegree : ℝ) - χ)) - mstWideC P s| * |iwRep ζ|) := by
          rw [habs]
      _ ≤ L * (R * |iwRep ζ|) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle (abs_nonneg _)) hLpos.le
      _ = L * R * ‖ζ‖ := by rw [norm_eq_abs_iwRep]; ring
  set Kd : ℝ := (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))) with hKddef
  set Bnd : ℝ := D * ((s : ℝ) + 1) ^ (-(δ * l)) * (L * R * (CΦ * Kd)) with hBnddef
  -- the profile bound
  have hprof : ∀ ζ : Circ, ‖ζ‖ * ‖mstProf P (2 ^ k) ζ‖ ≤ CΦ * Kd := by
    intro ζ
    simpa only [hKddef, neg_div] using hCΦ k hk1 ζ
  -- the pointwise term bound
  have hrewrite : ∀ β : Circ,
      star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β))
        - star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β)) * mstWideBump P χ η s (ξ - β))
      = star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β))
          * (mstEta P.natDegree χ η s (ξ - β) - mstWideBump P χ η s (ξ - β))) := by
    intro β; ring
  have hterm : ∀ β ∈ mstAnnulus l s,
      ‖star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β))
        - star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β)) * mstWideBump P χ η s (ξ - β))‖
      ≤ Bnd := by
    intro β hβ
    have hβ' : β ∈ mstU l (s + 1) \ mstU l s := by rwa [← hAeq]
    have hGβ : ‖mstG P β‖ ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)) := hGauss s β hβ'
    have hinner : ‖mstProf P (2 ^ k) (ξ - β)‖
        * ‖mstEta P.natDegree χ η s (ξ - β) - mstWideBump P χ η s (ξ - β)‖
        ≤ L * R * (CΦ * Kd) := by
      have hg := hdiff (ξ - β)
      have hp := hprof (ξ - β)
      calc ‖mstProf P (2 ^ k) (ξ - β)‖
              * ‖mstEta P.natDegree χ η s (ξ - β) - mstWideBump P χ η s (ξ - β)‖
          ≤ ‖mstProf P (2 ^ k) (ξ - β)‖ * (L * R * ‖ξ - β‖) :=
            mul_le_mul_of_nonneg_left hg (norm_nonneg _)
        _ = L * R * (‖ξ - β‖ * ‖mstProf P (2 ^ k) (ξ - β)‖) := by ring
        _ ≤ L * R * (CΦ * Kd) := by
            rw [hKddef]
            exact mul_le_mul_of_nonneg_left hp (mul_nonneg hLpos.le hRnn)
    rw [hrewrite β, hBnddef]
    simp only [norm_mul, norm_star]
    have hGnn : 0 ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)) :=
      mul_nonneg hD.le (Real.rpow_nonneg (by positivity) _)
    exact mul_le_mul hGβ hinner (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hGnn
  -- the sum bound
  have hsum : ‖mstNuS P l P.natDegree χ η k s ξ - mstWideModel P l χ η k s ξ‖ ≤ 2 * Bnd := by
    have hsym : mstNuS P l P.natDegree χ η k s ξ - mstWideModel P l χ η k s ξ
        = ∑ β ∈ mstAnnulus l s,
            (star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β))
              - star (mstG P β)
                  * (star (mstProf P (2 ^ k) (ξ - β)) * mstWideBump P χ η s (ξ - β))) := by
      rw [mstNuS_apply, mstWideModel_apply]
      rw [show mstAnnulus l s = mstLevel l (s + 1) \ mstLevel l s from rfl]
      rw [← Finset.sum_sub_distrib]
    rw [hsym]
    refine le_trans (norm_sum_le _ _) ?_
    have hZAZ : Z ⊆ mstAnnulus l s := Finset.filter_subset _ _
    have hzero : ∀ β ∈ mstAnnulus l s, β ∉ Z →
        ‖star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β))
          - star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β)) * mstWideBump P χ η s (ξ - β))‖
        = 0 := by
      intro β hβ hβZ
      have hg0 : mstEta P.natDegree χ η s (ξ - β) - mstWideBump P χ η s (ξ - β) = 0 := by
        by_contra hc
        exact hβZ (by rw [hZdef, Finset.mem_filter]; exact ⟨hβ, hc⟩)
      rw [hrewrite β, hg0]
      simp
    have hsumeq : ∑ β ∈ mstAnnulus l s,
          ‖star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β))
            - star (mstG P β)
                * (star (mstProf P (2 ^ k) (ξ - β)) * mstWideBump P χ η s (ξ - β))‖
        = ∑ β ∈ Z, ‖star (mstG P β)
            * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β))
            - star (mstG P β)
                * (star (mstProf P (2 ^ k) (ξ - β)) * mstWideBump P χ η s (ξ - β))‖ :=
      (Finset.sum_subset hZAZ hzero).symm
    rw [hsumeq]
    have hBndnn : 0 ≤ Bnd := by
      rw [hBnddef]
      have h2 : 0 ≤ Kd := by rw [hKddef]; exact Real.rpow_nonneg (by norm_num) _
      have h1 : 0 ≤ L * R * (CΦ * Kd) := mul_nonneg (mul_nonneg hLpos.le hRnn)
        (mul_nonneg hCΦpos.le h2)
      exact mul_nonneg (mul_nonneg hD.le (Real.rpow_nonneg (by positivity) _)) h1
    calc ∑ β ∈ Z, ‖star (mstG P β) * (star (mstProf P (2 ^ k) (ξ - β)) * mstEta P.natDegree χ η s (ξ - β))
              - star (mstG P β)
                  * (star (mstProf P (2 ^ k) (ξ - β)) * mstWideBump P χ η s (ξ - β))‖
        ≤ ∑ _β ∈ Z, Bnd :=
          Finset.sum_le_sum (fun β hβ => by
            rw [hZdef, Finset.mem_filter] at hβ
            exact hterm β hβ.1)
      _ = (Z.card : ℝ) * Bnd := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * Bnd := mul_le_mul_of_nonneg_right (by exact_mod_cast hZ2) hBndnn
  -- the final arithmetic
  have hRar : R * Kd ≤ (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))) := by
    have hA : ((2 ^ mstKappa P s : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hexp : ((2 ^ mstKappa P s : ℕ) : ℝ) / (2 * (P.natDegree : ℝ))
          + (-((k : ℝ) / (P.natDegree : ℝ)))
        = (((2 ^ mstKappa P s : ℕ) : ℝ) - 2 * (k : ℝ)) / (2 * (P.natDegree : ℝ)) := by
      have hne : (P.natDegree : ℝ) ≠ 0 := ne_of_gt hd0
      field_simp
      ring
    calc R * Kd
        = R * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))) := by rw [hKddef]
      _ ≤ (2 : ℝ) ^ (((2 ^ mstKappa P s : ℕ) : ℝ) / (2 * (P.natDegree : ℝ)))
            * (2 : ℝ) ^ (-((k : ℝ) / (P.natDegree : ℝ))) :=
          mul_le_mul_of_nonneg_right (by rw [hRdef]; exact hAr)
            (Real.rpow_nonneg (by norm_num) _)
      _ = (2 : ℝ) ^ (((2 ^ mstKappa P s : ℕ) : ℝ) / (2 * (P.natDegree : ℝ))
            + (-((k : ℝ) / (P.natDegree : ℝ)))) := by
          rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      _ ≤ (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))) := by
          rw [hexp]
          apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          rw [← neg_div]
          apply div_le_div_of_nonneg_right _ (by positivity)
          linarith
  have hBnd_le : 2 * Bnd ≤ (2 * L * CΦ + 1) * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
      * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))) := by
    have hDnn : 0 ≤ D * ((s : ℝ) + 1) ^ (-(δ * l)) :=
      mul_nonneg hD.le (Real.rpow_nonneg (by positivity) _)
    have h2nn : 0 ≤ (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))) :=
      Real.rpow_nonneg (by norm_num) _
    have hkey : (2 * L * CΦ) * (R * Kd)
        ≤ (2 * L * CΦ + 1) * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))) := by
      have h1 : (2 * L * CΦ) * (R * Kd) ≤ (2 * L * CΦ)
          * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))) :=
        mul_le_mul_of_nonneg_left hRar (by positivity)
      have h2 : (2 * L * CΦ) * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ))))
          ≤ (2 * L * CΦ + 1) * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))) :=
        mul_le_mul_of_nonneg_right (by linarith) h2nn
      linarith
    calc 2 * Bnd = (D * ((s : ℝ) + 1) ^ (-(δ * l))) * ((2 * L * CΦ) * (R * Kd)) := by
          rw [hBnddef]; ring
      _ ≤ (D * ((s : ℝ) + 1) ^ (-(δ * l)))
            * ((2 * L * CΦ + 1) * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ))))) :=
          mul_le_mul_of_nonneg_left hkey hDnn
      _ = (2 * L * CΦ + 1) * (D * ((s : ℝ) + 1) ^ (-(δ * l)))
            * (2 : ℝ) ^ (-((k : ℝ) / (2 * (P.natDegree : ℝ)))) := by ring
  exact le_trans hsum hBnd_le

end

end Work.Maximal
