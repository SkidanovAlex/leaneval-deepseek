/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The localised Seeley region estimate, in a clash-free dependency closure

This is a verbatim copy of `Submission/Work/NN/Final/seeleyRegionEstimate.lean` with the single
change that the gluing lemma `contDiffOn_glue_open` is taken from
`Submission/Work/NN/Final/flatOneSidedExtension.lean` rather than from the (identical) copy in
`Submission/Work/NN/Final/SeeleyLoc_glue.lean`.  The reason is that the latter declares a lemma
with the same name as the former, so that no module can import both; the present module belongs to
the `flatOneSidedExtension` dependency closure, which is also the closure of the one-sided
extension `Work.NN.PolarChain.one_sided_extension_finite`, and therefore the two can be used
together in the assembly of `Work.NN.Final.exists_extension_polar`.
-/
import Mathlib
import Submission.Work.NN.Final.SeeleyLoc
import Submission.Work.NN.Final.flatOneSidedExtension
import Submission.Work.NN.Final.holderDerivTendsto
import Submission.Work.NN.Final.seeleyLoc_term_gDN_le
import Submission.Work.NN.Final.seeleyLoc_term_gSN_le_uniform
import Submission.Work.NN.Final.seeleyLoc_continuousOn
import Submission.Work.NN.Final.seeleyLoc_iteratedFDeriv_eq_tsum
import Submission.Work.NN.Final.SeeleyJetMatchLower

noncomputable section

open scoped NNReal ENNReal ContDiff Topology BigOperators
open Set Filter

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Work.NN.Final

theorem seeleyRegionEstimateNoGlue {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {a b : ℕ → ℝ} (hb : ∀ m, 2 ≤ b m)
    (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (δ : ℝ) (_hδ : 0 < δ) (W : Set E) (g : E × ℝ → ℂ),
      IsOpen W →
      ContDiffOn ℝ (k : WithTop ENat) g (W ×ˢ {t : ℝ | 0 ≤ t}) →
      Work.CR.Flat.holderNorm k α g (W ×ˢ {t : ℝ | 0 < t}) ≠ ⊤ →
      ContDiffOn ℝ (k : WithTop ENat) (Work.NN.Final.seeleyExt a b g) (W ×ˢ {t : ℝ | -δ < t}) ∧
      Work.CR.Flat.holderNorm k α (Work.NN.Final.seeleyExt a b g) (W ×ˢ {t : ℝ | -δ < t})
        ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α g (W ×ˢ {t : ℝ | 0 < t}) := by
  classical
  have hb1 : ∀ m, 1 ≤ b m := fun m => le_trans (by norm_num) (hb m)
  have hbm0 : ∀ m, (0 : ℝ) ≤ b m := fun m => by linarith [hb m]
  -- the uniform termwise Hölder constant
  have hCSex : ∃ (CS : ℕ → ℝ), (∀ i, 0 < CS i) ∧
      ∀ (i : ℕ) (W : Set E) (hW : IsOpen W) (δ : ℝ) (g : E × ℝ → ℂ),
        ContDiffOn ℝ (i : WithTop ENat) g (seHp W) → ∀ m : ℕ,
        gSN i α (seeleyTerm a b g m) (seLw W δ)
          ≤ ENNReal.ofReal (|a m| * (b m) ^ (i + 2) * CS i)
            * (∑ j ∈ Finset.range (i + 1),
                (Work.CR.Flat.Holder.iDN j g (seUp W) + Work.CR.Flat.Holder.hSN j α g (seUp W))) := by
    refine ⟨fun i => Classical.choose
      (seeleyLoc_term_gSN_le_uniform (E := E) (a := a) (b := b) (i := i) hb1 hα0.le hα1.le), ?_, ?_⟩
    · intro i
      exact (Classical.choose_spec
        (seeleyLoc_term_gSN_le_uniform (E := E) (a := a) (b := b) (i := i) hb1 hα0.le hα1.le)).1
    · intro i W hW δ g hg m
      exact (Classical.choose_spec
        (seeleyLoc_term_gSN_le_uniform (E := E) (a := a) (b := b) (i := i) hb1 hα0.le hα1.le)).2
        W hW δ g hg m
  obtain ⟨CS, hCSpos, hCSbnd⟩ := hCSex
  -- the constants of the estimate
  set CD : ℕ → ℝ := fun i => ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j with hCD
  set AD : ℕ → ℝ := fun i => (i + 1) * CD i * (∑' m, |a m| * (b m) ^ i) with hAD
  set AS : ℕ → ℝ := fun i => 2 * (i + 1) * CS i * (∑' m, |a m| * (b m) ^ (i + 2)) with hAS
  set CC : ℕ → ℝ := fun k => (∑ i ∈ Finset.range (k + 1), (AD i + 1 + (AS i + 3))) + 1 with hCC
  have hADnn : ∀ i, 0 ≤ AD i := by
    intro i
    rw [hAD]
    refine mul_nonneg (mul_nonneg (by positivity) ?_) (tsum_nonneg fun m => ?_)
    · rw [hCD]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (seeleyCutB_nonneg j)
    · exact mul_nonneg (abs_nonneg _) (pow_nonneg (hbm0 m) i)
  have hASnn : ∀ i, 0 ≤ AS i := by
    intro i
    rw [hAS]
    refine mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (le_of_lt (hCSpos i))) ?_
    exact tsum_nonneg fun m => mul_nonneg (abs_nonneg _) (pow_nonneg (hbm0 m) (i + 2))
  refine ⟨CC, ?_, ?_⟩
  · intro k
    rw [hCC]
    have h : 0 ≤ ∑ i ∈ Finset.range (k + 1), (AD i + 1 + (AS i + 3)) :=
      Finset.sum_nonneg fun i _ => by have h1 := hADnn i; have h2 := hASnn i; linarith
    linarith
  · intro k δ hδ W g hW hg hfin
    set R : ℝ := (Work.CR.Flat.holderNorm k α g (seUp W)).toReal with hR
    have hofR : ENNReal.ofReal R = Work.CR.Flat.holderNorm k α g (seUp W) := by
      rw [hR]; exact ENNReal.ofReal_toReal hfin
    have hR0 : 0 ≤ R := by rw [hR]; exact ENNReal.toReal_nonneg
    have hUopen : IsOpen (seUp W) := isOpen_seUp hW
    have hSopen : IsOpen (seSl W δ) := isOpen_seSl hW δ
    have hgUp : ContDiffOn ℝ (k : WithTop ENat) g (seUp W) := hg.mono seUp_subset_seHp
    -- bounds on the derivatives of `g` on the open upper half space
    have hIDN : ∀ j ≤ k, ∀ z ∈ seUp W, ‖iteratedFDeriv ℝ j g z‖ ≤ R := by
      intro j hj z hz
      have h1 : Work.CR.Flat.iterDerivNorm j g (seUp W)
          ≤ Work.CR.Flat.holderNorm k α g (seUp W) :=
        Work.CR.Flat.iterDerivNorm_le_holderNorm k α g (seUp W) hj
      have h2 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ j g (seUp W) z‖ ≤ ENNReal.ofReal R := by
        rw [hofR]
        exact le_trans (Work.CR.Flat.le_iterDerivNorm j g (seUp W) hz) h1
      have h3 := (ENNReal.ofReal_le_ofReal_iff hR0).mp h2
      rwa [iteratedFDerivWithin_of_isOpen j hUopen hz] at h3
    have hHOL : ∀ j ≤ k, ∀ z ∈ seUp W, ∀ w ∈ seUp W, z ≠ w →
        ‖iteratedFDeriv ℝ j g z - iteratedFDeriv ℝ j g w‖ ≤ R * ‖z - w‖ ^ α := by
      intro j hj z hz w hw hzw
      have h1 : Work.CR.Flat.holderSeminorm j α g (seUp W)
          ≤ Work.CR.Flat.holderNorm k α g (seUp W) :=
        Work.CR.Flat.holderSeminorm_le_holderNorm k α g (seUp W) hj
      have h2 : ENNReal.ofReal (‖iteratedFDerivWithin ℝ j g (seUp W) z
            - iteratedFDerivWithin ℝ j g (seUp W) w‖ / ‖z - w‖ ^ α) ≤ ENNReal.ofReal R := by
        rw [hofR]
        exact le_trans (Work.CR.Flat.le_holderSeminorm j α g (seUp W) hz hw hzw) h1
      have h3 := (ENNReal.ofReal_le_ofReal_iff hR0).mp h2
      rw [iteratedFDerivWithin_of_isOpen j hUopen hz,
        iteratedFDerivWithin_of_isOpen j hUopen hw] at h3
      have hd : 0 < ‖z - w‖ ^ α := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzw)) α
      exact (div_le_iff₀ hd).mp h3
    -- the sum of the `C^{l,α}` norms of `g` on the upper half space
    have hSUMS : ∀ j ≤ k, (∑ l ∈ Finset.range (j + 1),
          (Work.CR.Flat.Holder.iDN l g (seUp W) + Work.CR.Flat.Holder.hSN l α g (seUp W)))
        ≤ ENNReal.ofReal (((2 : ℝ) * (j + 1)) * R) := by
      intro j hj
      have hterm : ∀ l ∈ Finset.range (j + 1),
          Work.CR.Flat.Holder.iDN l g (seUp W) + Work.CR.Flat.Holder.hSN l α g (seUp W)
            ≤ ENNReal.ofReal (2 * R) := by
        intro l hl
        have hlk : l ≤ k := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)) hj
        have h1 : Work.CR.Flat.Holder.iDN l g (seUp W) ≤ ENNReal.ofReal R := by
          rw [Work.CR.Flat.Holder.iDN_complex_eq, hofR]
          exact Work.CR.Flat.iterDerivNorm_le_holderNorm k α g (seUp W) hlk
        have h2 : Work.CR.Flat.Holder.hSN l α g (seUp W) ≤ ENNReal.ofReal R := by
          rw [Work.CR.Flat.Holder.hSN_complex_eq, hofR]
          exact Work.CR.Flat.holderSeminorm_le_holderNorm k α g (seUp W) hlk
        calc Work.CR.Flat.Holder.iDN l g (seUp W) + Work.CR.Flat.Holder.hSN l α g (seUp W)
            ≤ ENNReal.ofReal R + ENNReal.ofReal R := add_le_add h1 h2
          _ = ENNReal.ofReal (2 * R) := by
              rw [← ENNReal.ofReal_add hR0 hR0]
              congr 1
              ring
      calc (∑ l ∈ Finset.range (j + 1),
            (Work.CR.Flat.Holder.iDN l g (seUp W) + Work.CR.Flat.Holder.hSN l α g (seUp W)))
          ≤ ∑ _l ∈ Finset.range (j + 1), ENNReal.ofReal (2 * R) := Finset.sum_le_sum hterm
        _ = ENNReal.ofReal (((2 : ℝ) * (j + 1)) * R) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            push_cast
            ring
    have hSUMSDN : ∀ j ≤ k, (∑ l ∈ Finset.range (j + 1),
          Work.CR.Flat.Holder.iDN l g (seUp W)) ≤ ENNReal.ofReal (((j : ℝ) + 1) * R) := by
      intro j hj
      have hterm : ∀ l ∈ Finset.range (j + 1),
          Work.CR.Flat.Holder.iDN l g (seUp W) ≤ ENNReal.ofReal R := by
        intro l hl
        have hlk : l ≤ k := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)) hj
        rw [Work.CR.Flat.Holder.iDN_complex_eq, hofR]
        exact Work.CR.Flat.iterDerivNorm_le_holderNorm k α g (seUp W) hlk
      calc (∑ l ∈ Finset.range (j + 1), Work.CR.Flat.Holder.iDN l g (seUp W))
          ≤ ∑ _l ∈ Finset.range (j + 1), ENNReal.ofReal R := Finset.sum_le_sum hterm
        _ = ENNReal.ofReal (((j : ℝ) + 1) * R) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            push_cast
            ring
    have hCDnonneg : ∀ i, 0 ≤ CD i := by
      intro i; rw [hCD]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (seeleyCutB_nonneg j)
    -- ## Smoothness of the extension on the slab
    have hCont : ContDiffOn ℝ (k : WithTop ENat) (seeleyExt a b g) (seSl W δ) := by
      refine contDiffOn_glue_open hSopen ?hc ?hN ?hH ?hlim
      case hc =>
        refine seeleyLoc_continuousOn hb hbT (by simpa using ha 0) (by simpa using hsum 0)
          hW hδ hg.continuousOn
      case hN =>
        have hset : seSl W δ ∩ {p : E × ℝ | p.2 < 0} = seLw W δ := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_seSl, mem_seLw]
          tauto
        rw [hset]
        exact contDiffOn_seLw_seeleyExt hb hbT hW hgUp
      case hH =>
        have hset : seSl W δ ∩ {p : E × ℝ | 0 < p.2} = seUp W := by
          ext p
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, mem_seSl, mem_seUp]
          constructor
          · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨h1, by linarith⟩, h2⟩
        rw [hset]
        exact contDiffOn_seUp_seeleyExt hgUp
      case hlim =>
        intro i hi p hpS hp0
        simp only [mem_seSl] at hpS
        obtain ⟨L, hL₀⟩ := holderDerivTendsto hα0 hW g hfin hi hpS.1
        have hp_eq : ((p.1, (0 : ℝ)) : E × ℝ) = p := by rw [← hp0]
        have hL : Filter.Tendsto (fun q : E × ℝ => iteratedFDeriv ℝ i g q)
            (nhdsWithin p (seUp W)) (nhds L) := by
          rw [hp_eq] at hL₀
          exact hL₀
        refine ⟨L, ?_⟩
        have hsplit : seSl W δ ∩ {q : E × ℝ | q.2 ≠ 0}
            = (seSl W δ ∩ {q : E × ℝ | q.2 < 0}) ∪ (seSl W δ ∩ {q : E × ℝ | 0 < q.2}) := by
          ext q
          simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union]
          constructor
          · rintro ⟨h1, h2⟩
            rcases lt_or_gt_of_ne h2 with h3 | h3
            · exact Or.inl ⟨h1, h3⟩
            · exact Or.inr ⟨h1, h3⟩
          · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
            · exact ⟨h1, ne_of_lt h2⟩
            · exact ⟨h1, ne_of_gt h2⟩
        rw [hsplit, nhdsWithin_union p]
        refine tendsto_sup.mpr ⟨?_, ?_⟩
        · -- limit from below
          have hlow : Filter.Tendsto (fun q : E × ℝ => iteratedFDeriv ℝ i (seeleyExt a b g) q)
              (nhdsWithin p (seLw W δ)) (nhds L) :=
            (Work.NN.Final.JetMatch.seeleyJetMatchLower (a := a) (b := b) hb hbT ha hsum hW hfin hi
              (hg.of_le (by exact_mod_cast hi))
              (show p ∈ seHp W from by
                rw [mem_seHp]; exact ⟨hpS.1, le_of_eq hp0.symm⟩) hp0 hL).mono_left
              (nhdsWithin_mono p (by
                intro q hq
                simp only [mem_seLw] at hq
                exact hq.2.2))
          have hsub : (seSl W δ ∩ {q : E × ℝ | q.2 < 0}) ⊆ seLw W δ := by
            rintro q ⟨hq1, hq2⟩
            simp only [mem_seSl] at hq1
            exact ⟨hq1.1, hq1.2, hq2⟩
          exact hlow.mono_left (nhdsWithin_mono p hsub)
        · -- limit from above
          have hsub : (seSl W δ ∩ {q : E × ℝ | 0 < q.2}) ⊆ seUp W := by
            rintro q ⟨hq1, hq2⟩
            simp only [mem_seSl] at hq1
            exact ⟨hq1.1, hq2⟩
          have h1 : Filter.Tendsto (fun q : E × ℝ => iteratedFDeriv ℝ i g q)
              (nhdsWithin p (seSl W δ ∩ {q : E × ℝ | 0 < q.2})) (nhds L) :=
            hL.mono_left (nhdsWithin_mono p hsub)
          have hev : (fun q : E × ℝ => iteratedFDeriv ℝ i (seeleyExt a b g) q)
              =ᶠ[nhdsWithin p (seSl W δ ∩ {q : E × ℝ | 0 < q.2})]
              (fun q : E × ℝ => iteratedFDeriv ℝ i g q) := by
            filter_upwards [self_mem_nhdsWithin] with q hq
            have hq2 : 0 < q.2 := hq.2
            have heq : seeleyExt a b g =ᶠ[nhds q] g :=
              Filter.eventuallyEq_of_mem
                ((isOpen_lt continuous_const continuous_snd).mem_nhds hq2)
                (fun z hz => seeleyExt_of_nonneg a b g (le_of_lt hz))
            exact (heq.iteratedFDeriv ℝ i).self_of_nhds
          exact h1.congr' hev.symm
    -- ## Bound of `gDN i f` on the slab
    have hDN : ∀ i ≤ k, gDN i (seeleyExt a b g) (seSl W δ)
        ≤ ENNReal.ofReal ((AD i + 1) * R) := by
      intro i hi
      have hgi : ContDiffOn ℝ (i : WithTop ENat) g (seHp W) := hg.of_le (by exact_mod_cast hi)
      have hSumBound := hSUMS i hi
      have hDNbound := hSUMSDN i hi
      -- the bound on the open lower slab
      have hDNlow : ∀ z ∈ seLw W δ, ‖iteratedFDeriv ℝ i (seeleyExt a b g) z‖ ≤ AD i * R := by
        intro x hxV
        obtain ⟨hxW, hxδ, hxn⟩ := hxV
        have hxV' : x ∈ seLw W δ := ⟨hxW, hxδ, hxn⟩
        obtain ⟨N, hN⟩ := exists_b_ge hbT (4 / |x.2|)
        have hxabs : 0 < |x.2| := abs_pos.mpr (ne_of_lt hxn)
        have hN' : ∀ m ≥ N, 4 ≤ b m * |x.2| := by
          intro m hm
          have h1 : 4 / |x.2| ≤ b m := hN m hm
          rw [div_le_iff₀ hxabs] at h1
          linarith
        have htsum := seeleyLoc_iteratedFDeriv_eq_tsum (a := a) (b := b) hb hbT hW hgi hxV' hN'
        -- the pointwise bound for the terms
        have hterm : ∀ m : ℕ, ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) x‖
            ≤ (|a m| * (b m) ^ i * CD i) * (((i : ℝ) + 1) * R) := by
          intro m
          have hxV' : x ∈ seLw W (1 - x.2) := ⟨hxW, by linarith, hxn⟩
          have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) x‖
              ≤ gDN i (seeleyTerm a b g m) (seLw W (1 - x.2)) := le_gDN i hxV'
          have h2 : gDN i (seeleyTerm a b g m) (seLw W (1 - x.2))
              ≤ ENNReal.ofReal (|a m| * (b m) ^ i * CD i)
                * ENNReal.ofReal (((i : ℝ) + 1) * R) := by
            have h2a := seeleyLoc_term_gDN_le (a := a) (b := b) hb1 hW (δ := 1 - x.2)
              (i := i) hgi m
            calc gDN i (seeleyTerm a b g m) (seLw W (1 - x.2))
                ≤ ENNReal.ofReal (|a m| * (b m) ^ i *
                    (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j))
                  * (∑ j ∈ Finset.range (i + 1), Work.CR.Flat.Holder.iDN j g (seUp W)) := h2a
              _ = ENNReal.ofReal (|a m| * (b m) ^ i * CD i)
                  * (∑ j ∈ Finset.range (i + 1), Work.CR.Flat.Holder.iDN j g (seUp W)) := by
                    rw [show (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j)
                      = CD i from by rw [hCD]]
              _ ≤ ENNReal.ofReal (|a m| * (b m) ^ i * CD i)
                  * ENNReal.ofReal (((i : ℝ) + 1) * R) := mul_le_mul' le_rfl hDNbound
          have h3 : ENNReal.ofReal ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) x‖
              ≤ ENNReal.ofReal ((|a m| * (b m) ^ i * CD i) * (((i : ℝ) + 1) * R)) := by
            refine le_trans (le_trans h1 h2) ?_
            rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (abs_nonneg _)
              (pow_nonneg (hbm0 m) i)) (hCDnonneg i))]
          exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
            (pow_nonneg (hbm0 m) i)) (hCDnonneg i)) (mul_nonneg (by positivity) hR0))).mp h3
        -- summability and the comparison
        have hsm : Summable fun m : ℕ => |a m| * (b m) ^ i * CD i * (((i : ℝ) + 1) * R) :=
          ((hsum i).mul_right (CD i)).mul_right _
        have hsmn : Summable fun m : ℕ =>
            ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) x‖ :=
          Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm hsm
        have hfac : (∑' m, |a m| * (b m) ^ i * CD i * (((i : ℝ) + 1) * R))
            = (∑' m, |a m| * (b m) ^ i) * (CD i * (((i : ℝ) + 1) * R)) := by
          rw [show (fun m : ℕ => |a m| * (b m) ^ i * CD i * (((i : ℝ) + 1) * R))
              = (fun m : ℕ => (|a m| * (b m) ^ i) * (CD i * (((i : ℝ) + 1) * R))) from by
            funext m; ring]
          rw [tsum_mul_right]
        calc ‖iteratedFDeriv ℝ i (seeleyExt a b g) x‖
            = ‖∑' m, iteratedFDeriv ℝ i (seeleyTerm a b g m) x‖ := by rw [htsum]
          _ ≤ ∑' m, ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) x‖ :=
              norm_tsum_le_tsum_norm hsmn
          _ ≤ ∑' m, |a m| * (b m) ^ i * CD i * (((i : ℝ) + 1) * R) :=
              Summable.tsum_le_tsum hterm hsmn hsm
          _ = AD i * R := by
              rw [hfac, hAD]
              ring_nf
      -- the bound on the open upper half space
      have hDNup : ∀ z ∈ seUp W, ‖iteratedFDeriv ℝ i (seeleyExt a b g) z‖ ≤ R := by
        intro z hz
        have hev : seeleyExt a b g =ᶠ[nhds z] g :=
          Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_snd).mem_nhds hz.2)
            (fun w hw => seeleyExt_of_nonneg a b g (le_of_lt hw))
        have hEq : iteratedFDeriv ℝ i (seeleyExt a b g) z = iteratedFDeriv ℝ i g z :=
          (hev.iteratedFDeriv ℝ i).self_of_nhds
        rw [hEq]
        exact hIDN i hi z hz
      refine iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal ?_
      obtain ⟨hxW, hxδ⟩ := hx
      have hxS : x ∈ seSl W δ := ⟨hxW, hxδ⟩
      rcases lt_trichotomy x.2 0 with hxn | hxz | hxp
      · have h1 : ‖iteratedFDeriv ℝ i (seeleyExt a b g) x‖ ≤ AD i * R :=
          hDNlow x ⟨hxW, hxδ, hxn⟩
        calc ‖iteratedFDeriv ℝ i (seeleyExt a b g) x‖ ≤ AD i * R := h1
          _ ≤ (AD i + 1) * R := mul_le_mul_of_nonneg_right (by linarith [hADnn i]) hR0
      · -- the hyperplane line
        have hcont : ContinuousOn (fun q : E × ℝ => iteratedFDeriv ℝ i (seeleyExt a b g) q)
            (seSl W δ) :=
          ContinuousOn.continuousOn_iteratedFDeriv hCont hSopen (by exact_mod_cast hi)
        have hmem : ∀ᶠ t in 𝓝[<] (0 : ℝ), (x.1, t) ∈ seSl W δ := by
          have hOi : Set.Ioi (-δ) ∈ 𝓝[<] (0 : ℝ) :=
            Filter.mem_of_superset (Filter.mem_inf_of_left
              (isOpen_Ioi.mem_nhds (by linarith : (-δ : ℝ) < 0))) (by intro t ht; exact ht)
          filter_upwards [self_mem_nhdsWithin, hOi] with t ht htδ
          exact ⟨hxW, htδ⟩
        have hlim2 : Filter.Tendsto (fun t : ℝ => iteratedFDeriv ℝ i (seeleyExt a b g) (x.1, t))
            (𝓝[<] (0 : ℝ)) (nhds (iteratedFDeriv ℝ i (seeleyExt a b g) x)) := by
          have hφ : Filter.Tendsto (fun t : ℝ => (x.1, t)) (𝓝[<] (0 : ℝ)) (nhdsWithin x (seSl W δ)) := by
            refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
            · have h1 : Filter.Tendsto (fun t : ℝ => (x.1, t)) (nhds (0 : ℝ))
                  (nhds ((x.1, (0 : ℝ)) : E × ℝ)) :=
                (continuous_const.prodMk continuous_id).tendsto 0
              rw [show ((x.1, (0 : ℝ)) : E × ℝ) = x from by rw [← hxz]] at h1
              exact h1.mono_left nhdsWithin_le_nhds
            · exact hmem
          exact (hcont.continuousWithinAt hxS).tendsto.comp hφ
        have hbound : Filter.Tendsto
            (fun t : ℝ => ENNReal.ofReal ‖iteratedFDeriv ℝ i (seeleyExt a b g) (x.1, t)‖)
            (𝓝[<] (0 : ℝ)) (nhds (ENNReal.ofReal ‖iteratedFDeriv ℝ i (seeleyExt a b g) x‖)) :=
          ((ENNReal.continuous_ofReal.comp continuous_norm).tendsto _).comp hlim2
        have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ i (seeleyExt a b g) x‖
            ≤ ENNReal.ofReal (AD i * R) := by
          refine le_of_tendsto hbound ?_
          filter_upwards [self_mem_nhdsWithin, hmem] with t ht htm
          exact ENNReal.ofReal_le_ofReal (hDNlow (x.1, t) ⟨htm.1, htm.2, ht⟩)
        have h2 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (hADnn i) hR0)).mp h1
        calc ‖iteratedFDeriv ℝ i (seeleyExt a b g) x‖ ≤ AD i * R := h2
          _ ≤ (AD i + 1) * R := mul_le_mul_of_nonneg_right (by linarith [hADnn i]) hR0
      · -- the open upper half space
        have h1 : ‖iteratedFDeriv ℝ i (seeleyExt a b g) x‖ ≤ R := hDNup x ⟨hxW, hxp⟩
        calc ‖iteratedFDeriv ℝ i (seeleyExt a b g) x‖ ≤ R := h1
          _ ≤ (AD i + 1) * R := le_mul_of_one_le_left hR0 (by linarith [hADnn i])

    -- ## Bound of `gSN i α f` on the slab
    have hSN : ∀ i ≤ k, gSN i α (seeleyExt a b g) (seSl W δ)
        ≤ ENNReal.ofReal ((AS i + 3) * R) := by
      intro i hi
      have hgi : ContDiffOn ℝ (i : WithTop ENat) g (seHp W) := hg.of_le (by exact_mod_cast hi)
      have hSumBound := hSUMS i hi
      have hSumReal : ((∑ l ∈ Finset.range (i + 1),
            (Work.CR.Flat.Holder.iDN l g (seUp W)
              + Work.CR.Flat.Holder.hSN l α g (seUp W))).toReal) ≤ ((2 : ℝ) * (i + 1)) * R :=
        ENNReal.toReal_le_of_le_ofReal (by positivity) hSumBound
      have hcont : ContinuousOn (fun q : E × ℝ => iteratedFDeriv ℝ i (seeleyExt a b g) q)
          (seSl W δ) :=
        ContinuousOn.continuousOn_iteratedFDeriv hCont hSopen (by exact_mod_cast hi)
      -- the pointwise sup bound for the terms on any lower slab
      have htermDN : ∀ (δ' : ℝ) (z : E × ℝ), z ∈ seLw W δ' → ∀ m : ℕ,
          ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) z‖
            ≤ |a m| * (b m) ^ i * CD i * (((i : ℝ) + 1) * R) := by
        intro δ' z hz m
        have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) z‖
            ≤ gDN i (seeleyTerm a b g m) (seLw W δ') := le_gDN i hz
        have h2a := seeleyLoc_term_gDN_le (a := a) (b := b) hb1 hW (δ := δ') (i := i) hgi m
        have h2 : gDN i (seeleyTerm a b g m) (seLw W δ')
            ≤ ENNReal.ofReal (|a m| * (b m) ^ i * CD i) * ENNReal.ofReal (((i : ℝ) + 1) * R) := by
          calc gDN i (seeleyTerm a b g m) (seLw W δ')
              ≤ ENNReal.ofReal (|a m| * (b m) ^ i *
                  (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j))
                * (∑ j ∈ Finset.range (i + 1), Work.CR.Flat.Holder.iDN j g (seUp W)) := h2a
            _ = ENNReal.ofReal (|a m| * (b m) ^ i * CD i)
                * (∑ j ∈ Finset.range (i + 1), Work.CR.Flat.Holder.iDN j g (seUp W)) := by
                  rw [show (∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * seeleyCutB j)
                    = CD i from by rw [hCD]]
            _ ≤ ENNReal.ofReal (|a m| * (b m) ^ i * CD i)
                * ENNReal.ofReal (((i : ℝ) + 1) * R) := mul_le_mul' le_rfl (hSUMSDN i hi)
        have h3 : ENNReal.ofReal ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) z‖
            ≤ ENNReal.ofReal ((|a m| * (b m) ^ i * CD i) * (((i : ℝ) + 1) * R)) := by
          refine le_trans (le_trans h1 h2) ?_
          rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (abs_nonneg _)
            (pow_nonneg (hbm0 m) i)) (hCDnonneg i))]
        exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
          (pow_nonneg (hbm0 m) i)) (hCDnonneg i)) (mul_nonneg (by positivity) hR0))).mp h3
      -- the termwise Hölder bound on any lower slab
      have htermHOL : ∀ (δ' : ℝ) (z w : E × ℝ), z ∈ seLw W δ' → w ∈ seLw W δ' → z ≠ w →
          ∀ m : ℕ, ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) z
              - iteratedFDeriv ℝ i (seeleyTerm a b g m) w‖
            ≤ (|a m| * (b m) ^ (i + 2) * CS i) * (((2 : ℝ) * (i + 1)) * R) * ‖z - w‖ ^ α := by
        intro δ' z w hz hw hzw m
        have h1 : ENNReal.ofReal (‖iteratedFDeriv ℝ i (seeleyTerm a b g m) z
              - iteratedFDeriv ℝ i (seeleyTerm a b g m) w‖ / ‖z - w‖ ^ α)
            ≤ gSN i α (seeleyTerm a b g m) (seLw W δ') := le_gSN i α hz hw hzw
        have h2 := hCSbnd i W hW δ' g hgi m
        have h3 : ENNReal.ofReal (‖iteratedFDeriv ℝ i (seeleyTerm a b g m) z
              - iteratedFDeriv ℝ i (seeleyTerm a b g m) w‖ / ‖z - w‖ ^ α)
            ≤ ENNReal.ofReal ((|a m| * (b m) ^ (i + 2) * CS i)
                * (((2 : ℝ) * (i + 1)) * R)) := by
          calc ENNReal.ofReal (‖iteratedFDeriv ℝ i (seeleyTerm a b g m) z
                - iteratedFDeriv ℝ i (seeleyTerm a b g m) w‖ / ‖z - w‖ ^ α)
              ≤ ENNReal.ofReal (|a m| * (b m) ^ (i + 2) * CS i)
                * (∑ j ∈ Finset.range (i + 1),
                    (Work.CR.Flat.Holder.iDN j g (seUp W)
                      + Work.CR.Flat.Holder.hSN j α g (seUp W))) := le_trans h1 h2
            _ ≤ ENNReal.ofReal (|a m| * (b m) ^ (i + 2) * CS i)
                * ENNReal.ofReal (((2 : ℝ) * (i + 1)) * R) := mul_le_mul' le_rfl hSumBound
            _ = ENNReal.ofReal ((|a m| * (b m) ^ (i + 2) * CS i)
                  * (((2 : ℝ) * (i + 1)) * R)) := by
                  rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (abs_nonneg _)
                    (pow_nonneg (hbm0 m) (i + 2))) (le_of_lt (hCSpos i)))]
        have h4 := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
          (pow_nonneg (hbm0 m) (i + 2))) (le_of_lt (hCSpos i)))
          (mul_nonneg (by positivity) hR0))).mp h3
        have hd : 0 < ‖z - w‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hzw)) α
        exact (div_le_iff₀ hd).mp h4
      -- (a) both points in the closed upper half space
      have hPairUp : ∀ x ∈ seHp W, ∀ y ∈ seHp W, x ≠ y →
          ‖iteratedFDeriv ℝ i (seeleyExt a b g) x - iteratedFDeriv ℝ i (seeleyExt a b g) y‖
            / ‖x - y‖ ^ α ≤ R := by
        intro x hxH y hyH hxy
        simp only [mem_seHp] at hxH hyH
        have hxS : x ∈ seSl W δ := by
          simp only [mem_seSl]; exact ⟨hxH.1, by linarith [hxH.2]⟩
        have hyS : y ∈ seSl W δ := by
          simp only [mem_seSl]; exact ⟨hyH.1, by linarith [hyH.2]⟩
        have hφx : Filter.Tendsto (fun e : ℝ => ((x.1, x.2 + e) : E × ℝ)) (𝓝[>] (0 : ℝ))
            (nhdsWithin x (seSl W δ)) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
          · have h2 : Filter.Tendsto (fun e : ℝ => ((x.1, x.2 + e) : E × ℝ)) (nhds (0 : ℝ))
                (nhds ((x.1, x.2 + 0) : E × ℝ)) :=
              (continuous_const.prodMk (continuous_const.add continuous_id)).tendsto 0
            simpa using h2.mono_left nhdsWithin_le_nhds
          · have hOi : Set.Ioi (-δ) ∈ 𝓝[>] (0 : ℝ) := by
              filter_upwards [self_mem_nhdsWithin] with t ht
              exact lt_trans (by linarith : (-δ : ℝ) < 0) (Set.mem_Ioi.mp ht)
            filter_upwards [hOi] with e he
            simp only [mem_seSl]
            exact ⟨hxH.1, by linarith [hxH.2, Set.mem_Ioi.mp he]⟩
        have hφy : Filter.Tendsto (fun e : ℝ => ((y.1, y.2 + e) : E × ℝ)) (𝓝[>] (0 : ℝ))
            (nhdsWithin y (seSl W δ)) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
          · have h2 : Filter.Tendsto (fun e : ℝ => ((y.1, y.2 + e) : E × ℝ)) (nhds (0 : ℝ))
                (nhds ((y.1, y.2 + 0) : E × ℝ)) :=
              (continuous_const.prodMk (continuous_const.add continuous_id)).tendsto 0
            simpa using h2.mono_left nhdsWithin_le_nhds
          · have hOi : Set.Ioi (-δ) ∈ 𝓝[>] (0 : ℝ) := by
              filter_upwards [self_mem_nhdsWithin] with t ht
              exact lt_trans (by linarith : (-δ : ℝ) < 0) (Set.mem_Ioi.mp ht)
            filter_upwards [hOi] with e he
            simp only [mem_seSl]
            exact ⟨hyH.1, by linarith [hyH.2, Set.mem_Ioi.mp he]⟩
        have hnum : Filter.Tendsto
            (fun e : ℝ => ‖iteratedFDeriv ℝ i (seeleyExt a b g) (x.1, x.2 + e)
              - iteratedFDeriv ℝ i (seeleyExt a b g) (y.1, y.2 + e)‖ / ‖x - y‖ ^ α)
            (𝓝[>] (0 : ℝ))
            (nhds (‖iteratedFDeriv ℝ i (seeleyExt a b g) x
              - iteratedFDeriv ℝ i (seeleyExt a b g) y‖ / ‖x - y‖ ^ α)) :=
          (((hcont.continuousWithinAt hxS).tendsto.comp hφx).sub
            ((hcont.continuousWithinAt hyS).tendsto.comp hφy)).norm.div_const _
        refine le_of_tendsto hnum ?_
        filter_upwards [self_mem_nhdsWithin] with e he
        have he0 : 0 < e := Set.mem_Ioi.mp he
        have hxe : (x.1, x.2 + e) ∈ seUp W := by
          simp only [mem_seUp]; exact ⟨hxH.1, by linarith [hxH.2]⟩
        have hye : (y.1, y.2 + e) ∈ seUp W := by
          simp only [mem_seUp]; exact ⟨hyH.1, by linarith [hyH.2]⟩
        have hne : ((x.1, x.2 + e) : E × ℝ) ≠ (y.1, y.2 + e) := by
          intro h
          refine hxy (Prod.ext (Prod.ext_iff.mp h).1 ?_)
          have h2 := (Prod.ext_iff.mp h).2
          linarith
        have hd : (((x.1, x.2 + e) : E × ℝ) - (y.1, y.2 + e)) = x - y := by
          ext <;> simp
        have hfn : ∀ (z : E × ℝ), z ∈ seUp W →
            iteratedFDeriv ℝ i (seeleyExt a b g) z = iteratedFDeriv ℝ i g z := by
          intro z hz
          simp only [mem_seUp] at hz
          have hev : seeleyExt a b g =ᶠ[nhds z] g :=
            Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_snd).mem_nhds hz.2)
              (fun w hw => seeleyExt_of_nonneg a b g (le_of_lt hw))
          exact (hev.iteratedFDeriv ℝ i).self_of_nhds
        rw [hfn _ hxe, hfn _ hye]
        have hd0 : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
        rw [div_le_iff₀ hd0, ← hd]
        exact hHOL i hi _ hxe _ hye hne
      -- (c) both points in the open lower slab
      have hPairLow_aux : ∀ x ∈ seLw W δ, ∀ y ∈ seLw W δ, x ≠ y →
          ‖iteratedFDeriv ℝ i (seeleyExt a b g) x - iteratedFDeriv ℝ i (seeleyExt a b g) y‖
            / ‖x - y‖ ^ α ≤ (AS i + 2) * R := by
        intro x hxV y hyV hxy
        obtain ⟨hxW, hxδ, hxn⟩ := hxV
        obtain ⟨hyW, hyδ, hyn⟩ := hyV
        have hxV' : x ∈ seLw W δ := ⟨hxW, hxδ, hxn⟩
        have hyV' : y ∈ seLw W δ := ⟨hyW, hyδ, hyn⟩
        obtain ⟨Nx, hNx⟩ := exists_b_ge hbT (4 / |x.2|)
        obtain ⟨Ny, hNy⟩ := exists_b_ge hbT (4 / |y.2|)
        set N : ℕ := max Nx Ny with hN
        have hxabs : 0 < |x.2| := abs_pos.mpr (ne_of_lt hxn)
        have hNx' : ∀ m ≥ N, 4 ≤ b m * |x.2| := by
          intro m hm
          have h1 : 4 / |x.2| ≤ b m := hNx m (le_trans (le_max_left _ _) hm)
          rw [div_le_iff₀ hxabs] at h1
          linarith
        have hyabs : 0 < |y.2| := abs_pos.mpr (ne_of_lt hyn)
        have hNy' : ∀ m ≥ N, 4 ≤ b m * |y.2| := by
          intro m hm
          have h1 : 4 / |y.2| ≤ b m := hNy m (le_trans (le_max_right _ _) hm)
          rw [div_le_iff₀ hyabs] at h1
          linarith
        have htendx := seeleyLoc_iteratedFDeriv_eq_tsum (a := a) (b := b) hb hbT hW hgi hxV' hNx'
        have htendy := seeleyLoc_iteratedFDeriv_eq_tsum (a := a) (b := b) hb hbT hW hgi hyV' hNy'
        -- a common lower slab containing both points
        set δ' : ℝ := δ + 1 with hδ'
        have hδ'pos : 0 < δ' := by rw [hδ']; linarith
        have hxV'' : x ∈ seLw W δ' := by
          refine ⟨hxW, ?_, hxn⟩
          rw [hδ']; linarith
        have hyV'' : y ∈ seLw W δ' := by
          refine ⟨hyW, ?_, hyn⟩
          rw [hδ']; linarith
        have hsmw : Summable fun m : ℕ => |a m| * (b m) ^ i * CD i * (((i : ℝ) + 1) * R) :=
          ((hsum i).mul_right (CD i)).mul_right (((i : ℝ) + 1) * R)
        have hsmx : Summable fun m : ℕ => iteratedFDeriv ℝ i (seeleyTerm a b g m) x :=
          Summable.of_norm_bounded hsmw (fun m => htermDN δ' x hxV'' m)
        have hsmy : Summable fun m : ℕ => iteratedFDeriv ℝ i (seeleyTerm a b g m) y :=
          Summable.of_norm_bounded hsmw (fun m => htermDN δ' y hyV'' m)
        have hdiff : iteratedFDeriv ℝ i (seeleyExt a b g) x
            - iteratedFDeriv ℝ i (seeleyExt a b g) y
            = ∑' m, (iteratedFDeriv ℝ i (seeleyTerm a b g m) x
                - iteratedFDeriv ℝ i (seeleyTerm a b g m) y) := by
          rw [htendx, htendy]
          exact (Summable.tsum_sub hsmx hsmy).symm
        have hsm : Summable fun m : ℕ => |a m| * (b m) ^ (i + 2) * CS i
            * (((2 : ℝ) * (i + 1)) * R) * ‖x - y‖ ^ α :=
          (((hsum (i + 2)).mul_right (CS i)).mul_right (((2 : ℝ) * (i + 1)) * R)).mul_right _
        have hsmt : Summable fun m : ℕ => ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) x
            - iteratedFDeriv ℝ i (seeleyTerm a b g m) y‖ :=
          Summable.of_nonneg_of_le (fun m => norm_nonneg _)
            (fun m => htermHOL δ' x y hxV'' hyV'' hxy m) hsm
        have hmain : ‖iteratedFDeriv ℝ i (seeleyExt a b g) x
            - iteratedFDeriv ℝ i (seeleyExt a b g) y‖
            ≤ ((∑' m, |a m| * (b m) ^ (i + 2)) * (CS i * (((2 : ℝ) * (i + 1)) * R)))
              * ‖x - y‖ ^ α := by
          rw [hdiff]
          calc ‖∑' m, (iteratedFDeriv ℝ i (seeleyTerm a b g m) x
                - iteratedFDeriv ℝ i (seeleyTerm a b g m) y)‖
              ≤ ∑' m, ‖iteratedFDeriv ℝ i (seeleyTerm a b g m) x
                  - iteratedFDeriv ℝ i (seeleyTerm a b g m) y‖ := norm_tsum_le_tsum_norm hsmt
            _ ≤ ∑' m, ((|a m| * (b m) ^ (i + 2) * CS i) * (((2 : ℝ) * (i + 1)) * R))
                  * ‖x - y‖ ^ α :=
                Summable.tsum_le_tsum (fun m => htermHOL δ' x y hxV'' hyV'' hxy m) hsmt hsm
            _ = ((∑' m, |a m| * (b m) ^ (i + 2)) * (CS i * (((2 : ℝ) * (i + 1)) * R)))
                  * ‖x - y‖ ^ α := by
                rw [show (fun m : ℕ => ((|a m| * (b m) ^ (i + 2) * CS i)
                      * (((2 : ℝ) * (i + 1)) * R)) * ‖x - y‖ ^ α)
                    = (fun m : ℕ => (|a m| * (b m) ^ (i + 2)) *
                        (CS i * (((2 : ℝ) * (i + 1)) * R) * ‖x - y‖ ^ α)) from by
                  funext m; ring]
                rw [tsum_mul_right]
                ring
        have hd0 : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
        have hfac : (∑' m, |a m| * (b m) ^ (i + 2)) * (CS i * (((2 : ℝ) * (i + 1)) * R))
            = AS i * R := by
          rw [hAS]; ring
        refine le_trans ((div_le_iff₀ hd0).mpr hmain) ?_
        rw [hfac]
        exact mul_le_mul_of_nonneg_right (by linarith [hASnn i]) hR0
      -- (b) one point on the hyperplane line, the other in the open lower slab
      have hPairMid : ∀ x : E × ℝ, x.2 = 0 → x ∈ seSl W δ → ∀ y ∈ seLw W δ, x ≠ y →
          ‖iteratedFDeriv ℝ i (seeleyExt a b g) x - iteratedFDeriv ℝ i (seeleyExt a b g) y‖
            / ‖x - y‖ ^ α ≤ (AS i + 2) * R := by
        intro x hx0 hxS y hyV hxy
        simp only [mem_seSl] at hxS
        simp only [mem_seLw] at hyV
        have hφ : Filter.Tendsto (fun e : ℝ => ((x.1, -e) : E × ℝ)) (𝓝[>] (0 : ℝ))
            (nhdsWithin x (seSl W δ)) := by
          refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
          · have h2 : Filter.Tendsto (fun e : ℝ => ((x.1, -e) : E × ℝ)) (nhds (0 : ℝ))
                (nhds ((x.1, -(0 : ℝ)) : E × ℝ)) :=
              (continuous_const.prodMk continuous_neg).tendsto 0
            rw [show ((x.1, -(0 : ℝ)) : E × ℝ) = x from Prod.ext rfl (by rw [hx0, neg_zero])] at h2
            exact h2.mono_left nhdsWithin_le_nhds
          · have hOi : Set.Iio δ ∈ 𝓝[>] (0 : ℝ) :=
              (Filter.le_def.mp nhdsWithin_le_nhds) _ (isOpen_Iio.mem_nhds hδ)
            filter_upwards [hOi] with e he
            simp only [mem_seSl]
            exact ⟨hxS.1, by linarith [Set.mem_Iio.mp he]⟩
        have hxlim : Filter.Tendsto (fun e : ℝ => iteratedFDeriv ℝ i (seeleyExt a b g) (x.1, -e))
            (𝓝[>] (0 : ℝ)) (nhds (iteratedFDeriv ℝ i (seeleyExt a b g) x)) :=
          (hcont.continuousWithinAt hxS).tendsto.comp hφ
        have hxlim' : Filter.Tendsto (fun e : ℝ => ((x.1, -e) : E × ℝ)) (𝓝[>] (0 : ℝ)) (nhds x) := by
          have h2 : Filter.Tendsto (fun e : ℝ => ((x.1, -e) : E × ℝ)) (nhds (0 : ℝ))
              (nhds ((x.1, -(0 : ℝ)) : E × ℝ)) :=
            (continuous_const.prodMk continuous_neg).tendsto 0
          rw [show ((x.1, -(0 : ℝ)) : E × ℝ) = x from Prod.ext rfl (by rw [hx0, neg_zero])] at h2
          exact h2.mono_left nhdsWithin_le_nhds
        have hdist : Filter.Tendsto (fun e : ℝ => ‖((x.1, -e) : E × ℝ) - y‖ ^ α)
            (𝓝[>] (0 : ℝ)) (nhds (‖x - y‖ ^ α)) :=
          ((hxlim'.sub tendsto_const_nhds).norm).rpow tendsto_const_nhds (Or.inr hα0)
        have hd0 : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
        have hnum : Filter.Tendsto
            (fun e : ℝ => ‖iteratedFDeriv ℝ i (seeleyExt a b g) (x.1, -e)
              - iteratedFDeriv ℝ i (seeleyExt a b g) y‖ / ‖((x.1, -e) : E × ℝ) - y‖ ^ α)
            (𝓝[>] (0 : ℝ))
            (nhds (‖iteratedFDeriv ℝ i (seeleyExt a b g) x
              - iteratedFDeriv ℝ i (seeleyExt a b g) y‖ / ‖x - y‖ ^ α)) :=
          (hxlim.sub tendsto_const_nhds).norm.div hdist (ne_of_gt hd0)
        refine le_of_tendsto hnum ?_
        have hOδ : Set.Iio δ ∈ 𝓝[>] (0 : ℝ) :=
          (Filter.le_def.mp nhdsWithin_le_nhds) _ (isOpen_Iio.mem_nhds hδ)
        have hyneg : y.2 < 0 := by simpa using hyV.2.2
        have hOy : Set.Iio (-y.2) ∈ 𝓝[>] (0 : ℝ) :=
          (Filter.le_def.mp nhdsWithin_le_nhds) (Set.Iio (-y.2))
            (isOpen_Iio.mem_nhds (by linarith [hyneg] : (0 : ℝ) < -y.2))
        filter_upwards [self_mem_nhdsWithin, hOδ, hOy] with e he heδ heY
        have he0 : 0 < e := Set.mem_Ioi.mp he
        have hxe : ((x.1, -e) : E × ℝ) ∈ seLw W δ := by
          simp only [mem_seLw]
          exact ⟨hxS.1, by linarith [Set.mem_Iio.mp heδ], by linarith⟩
        have hne : ((x.1, -e) : E × ℝ) ≠ y := by
          intro h
          have h2 : -e = y.2 := (Prod.ext_iff.mp h).2
          have h1 : e < -y.2 := Set.mem_Iio.mp heY
          linarith [h1, h2]
        exact hPairLow_aux ((x.1, -e)) hxe y hyV hne
      have hPairMid' : ∀ x ∈ seLw W δ, ∀ y : E × ℝ, y.2 = 0 → y ∈ seSl W δ → x ≠ y →
          ‖iteratedFDeriv ℝ i (seeleyExt a b g) x - iteratedFDeriv ℝ i (seeleyExt a b g) y‖
            / ‖x - y‖ ^ α ≤ (AS i + 2) * R := by
        intro x hxV y hy0 hyS hxy
        have h := hPairMid y hy0 hyS x hxV (Ne.symm hxy)
        rw [norm_sub_rev (iteratedFDeriv ℝ i (seeleyExt a b g) x)
          (iteratedFDeriv ℝ i (seeleyExt a b g) y), norm_sub_rev x y]
        exact h
      -- (d) mixed case
      have hPairMix : ∀ x ∈ seUp W, ∀ y ∈ seLw W δ, x ≠ y →
          ‖iteratedFDeriv ℝ i (seeleyExt a b g) x - iteratedFDeriv ℝ i (seeleyExt a b g) y‖
            / ‖x - y‖ ^ α ≤ (AS i + 3) * R := by
        intro x hxU y hyV hxy
        simp only [mem_seUp] at hxU
        simp only [mem_seLw] at hyV
        set w : E × ℝ := (x.1, 0) with hw
        have hw0 : w.2 = 0 := by rw [hw]
        have hwS : w ∈ seSl W δ := by
          simp only [mem_seSl]
          exact ⟨hxU.1, by linarith⟩
        have hwH : w ∈ seHp W := by
          simp only [mem_seHp]
          exact ⟨hxU.1, by rw [hw]⟩
        have hxH : x ∈ seHp W := by
          simp only [mem_seHp]
          exact ⟨hxU.1, le_of_lt hxU.2⟩
        have hxw : x ≠ w := by
          intro h
          have h2 := (Prod.ext_iff.mp h).2
          rw [hw] at h2
          simp only at h2
          linarith [hxU.2]
        have hwy : w ≠ y := by
          intro h
          have h2 := (Prod.ext_iff.mp h).2
          rw [hw] at h2
          simp only at h2
          linarith [hyV.2.2]
        have h1 : ‖iteratedFDeriv ℝ i (seeleyExt a b g) x
            - iteratedFDeriv ℝ i (seeleyExt a b g) w‖ ≤ R * ‖x - w‖ ^ α := by
          have hq := hPairUp x hxH w hwH hxw
          have hd : 0 < ‖x - w‖ ^ α :=
            Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxw)) α
          exact (div_le_iff₀ hd).mp hq
        have h2 : ‖iteratedFDeriv ℝ i (seeleyExt a b g) w
            - iteratedFDeriv ℝ i (seeleyExt a b g) y‖ ≤ ((AS i + 2) * R) * ‖w - y‖ ^ α := by
          have hq := hPairMid w hw0 hwS y ⟨hyV.1, hyV.2.1, hyV.2.2⟩ hwy
          have hd : 0 < ‖w - y‖ ^ α :=
            Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hwy)) α
          exact (div_le_iff₀ hd).mp hq
        have hd1 : ‖x - w‖ ≤ ‖x - y‖ := Work.NN.Seeley.norm_sub_fst_zero_le hxU.2 hyV.2.2
        have hd2 : ‖w - y‖ ≤ ‖x - y‖ := Work.NN.Seeley.norm_sub_fst_zero_le' hxU.2 hyV.2.2
        have hp1 : ‖x - w‖ ^ α ≤ ‖x - y‖ ^ α := Real.rpow_le_rpow (norm_nonneg _) hd1 hα0.le
        have hp2 : ‖w - y‖ ^ α ≤ ‖x - y‖ ^ α := Real.rpow_le_rpow (norm_nonneg _) hd2 hα0.le
        have hd0 : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
        refine (div_le_iff₀ hd0).mpr ?_
        calc ‖iteratedFDeriv ℝ i (seeleyExt a b g) x - iteratedFDeriv ℝ i (seeleyExt a b g) y‖
            ≤ ‖iteratedFDeriv ℝ i (seeleyExt a b g) x - iteratedFDeriv ℝ i (seeleyExt a b g) w‖
              + ‖iteratedFDeriv ℝ i (seeleyExt a b g) w
                  - iteratedFDeriv ℝ i (seeleyExt a b g) y‖ := by
                rw [show iteratedFDeriv ℝ i (seeleyExt a b g) x
                    - iteratedFDeriv ℝ i (seeleyExt a b g) y
                    = (iteratedFDeriv ℝ i (seeleyExt a b g) x
                        - iteratedFDeriv ℝ i (seeleyExt a b g) w)
                      + (iteratedFDeriv ℝ i (seeleyExt a b g) w
                        - iteratedFDeriv ℝ i (seeleyExt a b g) y) from by abel]
                exact norm_add_le _ _
          _ ≤ R * ‖x - w‖ ^ α + ((AS i + 2) * R) * ‖w - y‖ ^ α := add_le_add h1 h2
          _ ≤ R * ‖x - y‖ ^ α + ((AS i + 2) * R) * ‖x - y‖ ^ α :=
              add_le_add (mul_le_mul_of_nonneg_left hp1 hR0)
                (mul_le_mul_of_nonneg_left hp2 (mul_nonneg (by linarith [hASnn i]) hR0))
          _ = (AS i + 3) * R * ‖x - y‖ ^ α := by ring
      have hPairMix' : ∀ x ∈ seLw W δ, ∀ y ∈ seUp W, x ≠ y →
          ‖iteratedFDeriv ℝ i (seeleyExt a b g) x - iteratedFDeriv ℝ i (seeleyExt a b g) y‖
            / ‖x - y‖ ^ α ≤ (AS i + 3) * R := by
        intro x hxV y hyU hxy
        have h := hPairMix y hyU x hxV (Ne.symm hxy)
        rw [norm_sub_rev (iteratedFDeriv ℝ i (seeleyExt a b g) x)
          (iteratedFDeriv ℝ i (seeleyExt a b g) y), norm_sub_rev x y]
        exact h
      -- the case analysis
      refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy =>
        ENNReal.ofReal_le_ofReal ?_
      obtain ⟨hxW, hxδ⟩ := hx
      obtain ⟨hyW, hyδ⟩ := hy
      have hxS : x ∈ seSl W δ := ⟨hxW, hxδ⟩
      have hyS : y ∈ seSl W δ := ⟨hyW, hyδ⟩
      have hp_mem : ∀ z : E × ℝ, z.1 ∈ W → 0 ≤ z.2 → z ∈ seHp W := fun z h1 h2 => by
        simp only [mem_seHp]; exact ⟨h1, h2⟩
      have h3 : (AS i + 2) * R ≤ (AS i + 3) * R :=
        mul_le_mul_of_nonneg_right (by linarith) hR0
      have h1 : R ≤ (AS i + 3) * R := by
        have hle : (1 : ℝ) ≤ AS i + 3 := by linarith [hASnn i]
        calc R = 1 * R := (one_mul R).symm
          _ ≤ (AS i + 3) * R := mul_le_mul_of_nonneg_right hle hR0
      rcases lt_trichotomy x.2 0 with hxn | hxz | hxp
      · rcases lt_trichotomy y.2 0 with hyn | hyz | hyp
        · exact le_trans (hPairLow_aux x ⟨hxW, hxδ, hxn⟩ y ⟨hyW, hyδ, hyn⟩ hxy) h3
        · exact le_trans (hPairMid' x ⟨hxW, hxδ, hxn⟩ y hyz hyS hxy) h3
        · exact le_trans (hPairMix' x ⟨hxW, hxδ, hxn⟩ y ⟨hyW, hyp⟩ hxy) (le_of_eq rfl)
      · rcases lt_trichotomy y.2 0 with hyn | hyz | hyp
        · exact le_trans (hPairMid x hxz hxS y ⟨hyW, hyδ, hyn⟩ hxy) h3
        · exact le_trans (hPairUp x (hp_mem x hxW (le_of_eq hxz.symm))
            y (hp_mem y hyW (le_of_eq hyz.symm)) hxy) h1
        · exact le_trans (hPairUp x (hp_mem x hxW (le_of_eq hxz.symm))
            y (hp_mem y hyW (le_of_lt hyp)) hxy) h1
      · rcases lt_trichotomy y.2 0 with hyn | hyz | hyp
        · exact le_trans (hPairMix x ⟨hxW, hxp⟩ y ⟨hyW, hyδ, hyn⟩ hxy) (le_of_eq rfl)
        · exact le_trans (hPairUp x (hp_mem x hxW (le_of_lt hxp))
            y (hp_mem y hyW (le_of_eq hyz.symm)) hxy) h1
        · exact le_trans (hPairUp x (hp_mem x hxW (le_of_lt hxp))
            y (hp_mem y hyW (le_of_lt hyp)) hxy) h1
    -- ## the final assembly
    have hFsplit : Work.CR.Flat.holderNorm k α (seeleyExt a b g) (seSl W δ)
        = ∑ i ∈ Finset.range (k + 1),
            (gDN i (seeleyExt a b g) (seSl W δ)
              + gSN i α (seeleyExt a b g) (seSl W δ)) := by
      unfold Work.CR.Flat.holderNorm
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      · exact (gDN_eq_iDN hSopen i (seeleyExt a b g)).symm
      · exact (gSN_eq_hSN hSopen i α (seeleyExt a b g)).symm
    refine ⟨hCont, ?_⟩
    change Work.CR.Flat.holderNorm k α (seeleyExt a b g) (seSl W δ)
        ≤ ENNReal.ofReal (CC k) * Work.CR.Flat.holderNorm k α g (seUp W)
    rw [hFsplit]
    calc ∑ i ∈ Finset.range (k + 1), (gDN i (seeleyExt a b g) (seSl W δ)
            + gSN i α (seeleyExt a b g) (seSl W δ))
        ≤ ∑ i ∈ Finset.range (k + 1),
            (ENNReal.ofReal ((AD i + 1) * R) + ENNReal.ofReal ((AS i + 3) * R)) :=
          Finset.sum_le_sum fun i hi' => add_le_add
            (hDN i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')))
            (hSN i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')))
      _ = (∑ i ∈ Finset.range (k + 1),
            (ENNReal.ofReal (AD i + 1) + ENNReal.ofReal (AS i + 3))) * ENNReal.ofReal R := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_mul (by linarith [hADnn i]), ENNReal.ofReal_mul (by linarith [hASnn i]),
            add_mul]
      _ ≤ ENNReal.ofReal (CC k) * ENNReal.ofReal R := by
          refine mul_le_mul' ?_ le_rfl
          have h1 : (∑ i ∈ Finset.range (k + 1),
                (ENNReal.ofReal (AD i + 1) + ENNReal.ofReal (AS i + 3)))
              = ENNReal.ofReal ((∑ i ∈ Finset.range (k + 1), (AD i + 1))
                  + ∑ i ∈ Finset.range (k + 1), (AS i + 3)) := by
            rw [Finset.sum_add_distrib,
              ← ENNReal.ofReal_sum_of_nonneg (f := fun i => AD i + 1)
                (fun i _ => by linarith [hADnn i]),
              ← ENNReal.ofReal_sum_of_nonneg (f := fun i => AS i + 3)
                (fun i _ => by linarith [hASnn i]),
              ← ENNReal.ofReal_add (Finset.sum_nonneg fun i _ => by linarith [hADnn i])
                (Finset.sum_nonneg fun i _ => by linarith [hASnn i])]
          rw [h1]
          rw [show CC k = (∑ i ∈ Finset.range (k + 1), (AD i + 1 + (AS i + 3))) + 1 from by
            rw [hCC]]
          refine ENNReal.ofReal_le_ofReal ?_
          have h2 : (∑ i ∈ Finset.range (k + 1), (AD i + 1 + (AS i + 3)))
              = (∑ i ∈ Finset.range (k + 1), (AD i + 1))
                + ∑ i ∈ Finset.range (k + 1), (AS i + 3) := Finset.sum_add_distrib
          rw [h2]
          linarith
      _ = ENNReal.ofReal (CC k) * Work.CR.Flat.holderNorm k α g (seUp W) := by rw [← hofR]

end Work.NN.Final
