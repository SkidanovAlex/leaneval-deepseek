import Mathlib
import Submission.Work.NN.Seeley.Setup
import Submission.Work.NN.Seeley.Glob
import Submission.Work.NN.Seeley.seeleyTV_iDN_le
import Submission.Work.NN.Seeley.seeleyTV_hSN_le
import Submission.Work.NN.Seeley.iteratedFDeriv_seeleySumV_of_neg
import Submission.Work.NN.Seeley.seeleyEV_contDiffOn
import Submission.Work.NN.Seeley.gDN_halfspace_closed_le
import Submission.Work.NN.Seeley.gSN_halfspace_closed_le
import Submission.Work.NN.Seeley.gDN_lower_halfspace_closed_le
import Submission.Work.NN.Seeley.gSN_lower_halfspace_closed_le
import Submission.Work.NN.Seeley.seeleyTV_iDN_le_uniform
import Submission.Work.NN.Seeley.seeleyTV_hSN_le_uniform
import Submission.Work.NN.Seeley.ofReal_norm_iteratedFDeriv_le_gDN_halfspace
import Submission.Work.NN.Seeley.ofReal_ratio_le_gSN_halfspace
import Submission.Work.NN.Seeley.ratio_le_closed_lower_of_le_open_lower

noncomputable section

open scoped NNReal ENNReal ContDiff Topology BigOperators
open Set Filter

set_option linter.unusedSectionVars false

namespace Work.NN.Seeley

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Projection to the hyperplane does not increase the distance to a point of the lower open
slab. -/
lemma norm_sub_fst_zero_le {p q : X × ℝ} (hp : 0 < p.2) (hq : q.2 < 0) :
    ‖p - ((p.1, 0) : X × ℝ)‖ ≤ ‖p - q‖ := by
  have h1 : p - ((p.1, 0) : X × ℝ) = (((0 : X), p.2) : X × ℝ) := by ext <;> simp
  have h2 : p - q = ((p.1 - q.1, p.2 - q.2) : X × ℝ) := rfl
  rw [h1, h2, Prod.norm_mk, Prod.norm_mk, norm_zero, Real.norm_eq_abs, abs_of_pos hp,
    max_eq_right hp.le]
  have h4 : p.2 ≤ |p.2 - q.2| := by
    rw [abs_of_pos (by linarith : (0:ℝ) < p.2 - q.2)]
    linarith
  exact h4.trans (le_max_right _ _)

/-- Projection to the hyperplane does not increase the distance from a point of the lower open
slab. -/
lemma norm_sub_fst_zero_le' {p q : X × ℝ} (hp : 0 < p.2) (hq : q.2 < 0) :
    ‖((p.1, 0) : X × ℝ) - q‖ ≤ ‖p - q‖ := by
  have h1 : ((p.1, 0) : X × ℝ) - q = ((p.1 - q.1, -q.2) : X × ℝ) := by ext <;> simp
  have h2 : p - q = ((p.1 - q.1, p.2 - q.2) : X × ℝ) := rfl
  rw [h1, h2, Prod.norm_mk, Prod.norm_mk]
  refine max_le (le_max_left _ _) ?_
  rw [Real.norm_eq_abs, abs_neg, abs_of_neg hq]
  have h5 : -q.2 ≤ |p.2 - q.2| := by
    have h6 : -q.2 ≤ p.2 - q.2 := by linarith
    exact h6.trans (le_abs_self _)
  exact h5.trans (le_max_right _ _)


variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma norm_iteratedFDerivWithin_le_of_iDN_le {i : ℕ} {f : X → ℂ} {Ω : Set X} {R : ℝ}
    (hR : 0 ≤ R) (h : Work.CR.Flat.Holder.iDN i f Ω ≤ ENNReal.ofReal R) {x : X} (hx : x ∈ Ω) :
    ‖iteratedFDerivWithin ℝ i f Ω x‖ ≤ R :=
  (ENNReal.ofReal_le_ofReal_iff hR).mp (le_trans (Work.CR.Flat.Holder.le_iDN i hx) h)

lemma ratio_le_of_hSN_le {i : ℕ} {α : ℝ} {f : X → ℂ} {Ω : Set X} {R : ℝ}
    (hR : 0 ≤ R) (h : Work.CR.Flat.Holder.hSN i α f Ω ≤ ENNReal.ofReal R)
    {x y : X} (hx : x ∈ Ω) (hy : y ∈ Ω) (hxy : x ≠ y) :
    ‖iteratedFDerivWithin ℝ i f Ω x - iteratedFDerivWithin ℝ i f Ω y‖ / ‖x - y‖ ^ α ≤ R :=
  (ENNReal.ofReal_le_ofReal_iff hR).mp (le_trans (Work.CR.Flat.Holder.le_hSN i α hx hy hxy) h)

end Work.NN.Seeley

namespace Work.NN.Seeley

open scoped BigOperators

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The `C^{k,α}` estimate for the Seeley extension: the extension operator does not increase the
Hölder norms, up to constants.  Write `holderNorm k α F slab` as the sum, over `i ≤ k`, of the
sup-norms and Hölder seminorms of the iterated derivatives over the slab (they agree with the
within-derivatives because the slab is open), and split the slab into the open upper half space
`{0 < p.2}`, the hyperplane `{p.2 = 0}` and the open lower slab `{-δ < p.2 ∧ p.2 < 0}`.  On the
upper half space `seeleyEV = g`; on the hyperplane the derivatives of `seeleyEV` equal those of `g`
because `seeleyEV` is `C^i` there (`seeleyEV_contDiffOn`) and equals `g` on the upper half space
(approximate the boundary point from above); on the lower slab `seeleyEV = seeleySumV`, whose
derivatives are the termwise series (`iteratedFDeriv_seeleySumV_of_neg`), bounded with the
uniform-in-`m` constants of `seeleyTV_iDN_le`/`seeleyTV_hSN_le`; summing against
`Σ_m |a m| (b m)^K < ∞` (`hsum`) gives the bounds.  The pairs straddling the hyperplane are
controlled by the same three ingredients together with the closure lemmas
(`gDN_halfspace_closed_le`, `gSN_halfspace_closed_le` and their lower-half-space analogues). -/
theorem seeleyEV_holderNorm_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδ : 0 < δ) (a b : ℕ → ℝ)
    (hb : ∀ m, 2 ≤ b m) (hbT : Filter.Tendsto b Filter.atTop Filter.atTop)
    (ha : ∀ j : ℕ, ∑' m, a m * (-(b m)) ^ j = 1)
    (hsum : ∀ j : ℕ, Summable fun m => |a m| * (b m) ^ j) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ g : X × ℝ → ℂ,
      (∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) g {p : X × ℝ | -δ < p.2}) →
      ∀ k : ℕ, Work.CR.Flat.holderNorm k α (Work.NN.Final.seeleyEV a b δ g)
          {p : X × ℝ | -δ < p.2}
        ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α g {p : X × ℝ | 0 < p.2} := by
  have hb1 : ∀ m, 1 ≤ b m := fun m => le_trans (by norm_num) (hb m)
  have hbmnn : ∀ m, (0 : ℝ) ≤ b m := fun m => by linarith [hb m]
  choose CD hCD using fun i : ℕ => seeleyTV_iDN_le_uniform (X := X) (a := a) (b := b) hδ hb1 i
  choose CS hCS using fun i : ℕ => seeleyTV_hSN_le_uniform (X := X) (a := a) (b := b) hδ hα0.le hα1.le hb1 i
  set AD : ℕ → ℝ := fun i => (∑' m, |a m| * (b m) ^ i) * CD i with hAD
  set AS : ℕ → ℝ := fun i => (∑' m, |a m| * (b m) ^ (i + 2)) * CS i with hAS
  have hADnn : ∀ i, 0 ≤ AD i := fun i => by
    rw [hAD]
    exact mul_nonneg (tsum_nonneg fun m => mul_nonneg (abs_nonneg _) (pow_nonneg (hbmnn m) i))
      (le_of_lt (hCD i).1)
  have hASnn : ∀ i, 0 ≤ AS i := fun i => by
    rw [hAS]
    exact mul_nonneg
      (tsum_nonneg fun m => mul_nonneg (abs_nonneg _) (pow_nonneg (hbmnn m) (i + 2)))
      (le_of_lt (hCS i).1)
  set Cfun : ℕ → ℝ := fun k => (∑ i ∈ Finset.range (k + 1), (AD i + 1 + (AS i + 2))) + 1
    with hCfun
  have hCfunpos : ∀ k, 0 < Cfun k := by
    intro k
    rw [hCfun]
    have h1 : 0 ≤ ∑ i ∈ Finset.range (k + 1), (AD i + 1 + (AS i + 2)) :=
      Finset.sum_nonneg fun i _ => by have h2 := hADnn i; have h3 := hASnn i; linarith
    linarith
  refine ⟨Cfun, hCfunpos, ?_⟩
  intro g hg k
  set S : Set (X × ℝ) := {p : X × ℝ | -δ < p.2} with hSdef
  set U : Set (X × ℝ) := {p : X × ℝ | 0 < p.2} with hUdef
  have hSopen : IsOpen S := by
    rw [hSdef]; exact isOpen_lt continuous_const continuous_snd
  have hUopen : IsOpen U := by
    rw [hUdef]; exact isOpen_lt continuous_const continuous_snd
  have hAopen : IsOpen {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} :=
    (isOpen_lt continuous_const continuous_snd).inter
      (isOpen_lt continuous_snd continuous_const)
  by_cases hTk : Work.CR.Flat.holderNorm k α g U = ⊤
  · rw [hTk, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (hCfunpos k)))]
    exact le_top
  · set R : ℝ := (Work.CR.Flat.holderNorm k α g U).toReal with hRdef
    have hofR : ENNReal.ofReal R = Work.CR.Flat.holderNorm k α g U := ENNReal.ofReal_toReal hTk
    have hR0 : 0 ≤ R := ENNReal.toReal_nonneg
    have hgDNle : ∀ j ≤ k, Work.NN.Final.gDN j g U ≤ ENNReal.ofReal R := by
      intro j hj
      rw [Work.NN.Final.gDN_eq_iDN hUopen j g, hofR]
      exact Work.CR.Flat.iterDerivNorm_le_holderNorm k α g U hj
    have hgpts : ∀ j ≤ k, ∀ x ∈ U, ‖iteratedFDeriv ℝ j g x‖ ≤ R := by
      intro j hj x hx
      exact (ENNReal.ofReal_le_ofReal_iff hR0).mp
        (le_trans (Work.NN.Final.le_gDN j hx) (hgDNle j hj))
    have hgpair : ∀ j ≤ k, ∀ x ∈ U, ∀ y ∈ U, x ≠ y →
        ‖iteratedFDeriv ℝ j g x - iteratedFDeriv ℝ j g y‖ / ‖x - y‖ ^ α ≤ R := by
      intro j hj x hx y hy hxy
      refine (ENNReal.ofReal_le_ofReal_iff hR0).mp
        (le_trans (Work.NN.Final.le_gSN j α hx hy hxy) ?_)
      rw [hofR, Work.NN.Final.gSN_eq_hSN hUopen j α g]
      exact Work.CR.Flat.holderSeminorm_le_holderNorm k α g U hj
    have hSumDV : ∀ i ≤ k, (∑ j ∈ Finset.range (i + 1),
        Work.CR.Flat.Holder.iDN j g U) ≤ ENNReal.ofReal R := by
      intro i hi
      calc (∑ j ∈ Finset.range (i + 1), Work.CR.Flat.Holder.iDN j g U)
          = ∑ j ∈ Finset.range (i + 1), Work.CR.Flat.iterDerivNorm j g U :=
            Finset.sum_congr rfl fun j _ => Work.CR.Flat.Holder.iDN_complex_eq j g U
        _ ≤ ∑ j ∈ Finset.range (i + 1),
              (Work.CR.Flat.iterDerivNorm j g U + Work.CR.Flat.holderSeminorm j α g U) :=
            Finset.sum_le_sum fun j _ => le_add_right le_rfl
        _ = Work.CR.Flat.holderNorm i α g U := rfl
        _ ≤ Work.CR.Flat.holderNorm k α g U := Work.CR.Flat.holderNorm_mono_k hi α g U
        _ = ENNReal.ofReal R := hofR.symm
    have hSumSNV : ∀ i ≤ k, (∑ j ∈ Finset.range (i + 1),
        (Work.CR.Flat.Holder.iDN j g U + Work.CR.Flat.Holder.hSN j α g U))
        ≤ ENNReal.ofReal R := by
      intro i hi
      calc (∑ j ∈ Finset.range (i + 1),
            (Work.CR.Flat.Holder.iDN j g U + Work.CR.Flat.Holder.hSN j α g U))
          = ∑ j ∈ Finset.range (i + 1),
              (Work.CR.Flat.iterDerivNorm j g U + Work.CR.Flat.holderSeminorm j α g U) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Work.CR.Flat.Holder.iDN_complex_eq, Work.CR.Flat.Holder.hSN_complex_eq]
        _ = Work.CR.Flat.holderNorm i α g U := rfl
        _ ≤ Work.CR.Flat.holderNorm k α g U := Work.CR.Flat.holderNorm_mono_k hi α g U
        _ = ENNReal.ofReal R := hofR.symm
    have htermDN : ∀ i ≤ k, ∀ m : ℕ, ∀ x ∈ {p : X × ℝ | -δ < p.2 ∧ p.2 < 0},
        ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x‖
          ≤ |a m| * (b m) ^ i * CD i * R := by
      intro i hi m x hx
      have hxw : iteratedFDerivWithin ℝ i (Work.NN.Final.seeleyTV a b δ g m)
          {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} x
          = iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x :=
        iteratedFDerivWithin_of_isOpen i hAopen hx
      have h1 : Work.CR.Flat.Holder.iDN i (Work.NN.Final.seeleyTV a b δ g m)
          {p : X × ℝ | -δ < p.2 ∧ p.2 < 0}
          ≤ ENNReal.ofReal (|a m| * (b m) ^ i * CD i) *
            (∑ j ∈ Finset.range (i + 1), Work.CR.Flat.Holder.iDN j g U) :=
        (hCD i).2 g hg m
      have h2 : ENNReal.ofReal ‖iteratedFDerivWithin ℝ i (Work.NN.Final.seeleyTV a b δ g m)
            {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} x‖
          ≤ Work.CR.Flat.Holder.iDN i (Work.NN.Final.seeleyTV a b δ g m)
              {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} :=
        Work.CR.Flat.Holder.le_iDN i hx
      have h3 : ENNReal.ofReal (|a m| * (b m) ^ i * CD i) *
            (∑ j ∈ Finset.range (i + 1), Work.CR.Flat.Holder.iDN j g U)
          ≤ ENNReal.ofReal (|a m| * (b m) ^ i * CD i * R) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (abs_nonneg _)
          (pow_nonneg (hbmnn m) i)) (le_of_lt (hCD i).1))]
        exact mul_le_mul' le_rfl (hSumDV i hi)
      have h5 : ‖iteratedFDerivWithin ℝ i (Work.NN.Final.seeleyTV a b δ g m)
            {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} x‖ ≤ |a m| * (b m) ^ i * CD i * R :=
        (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
          (pow_nonneg (hbmnn m) i)) (le_of_lt (hCD i).1)) hR0)).mp (h2.trans (h1.trans h3))
      rw [← hxw]
      exact h5
    have htermSN : ∀ i ≤ k, ∀ m : ℕ, ∀ x y : X × ℝ,
        x ∈ {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} →
        y ∈ {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} → x ≠ y →
        ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x
          - iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) y‖ / ‖x - y‖ ^ α
          ≤ |a m| * (b m) ^ (i + 2) * CS i * R := by
      intro i hi m x y hx hy hxy
      have hxw : iteratedFDerivWithin ℝ i (Work.NN.Final.seeleyTV a b δ g m)
          {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} x
          = iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x :=
        iteratedFDerivWithin_of_isOpen i hAopen hx
      have hyw : iteratedFDerivWithin ℝ i (Work.NN.Final.seeleyTV a b δ g m)
          {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} y
          = iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) y :=
        iteratedFDerivWithin_of_isOpen i hAopen hy
      have h1 : Work.CR.Flat.Holder.hSN i α (Work.NN.Final.seeleyTV a b δ g m)
          {p : X × ℝ | -δ < p.2 ∧ p.2 < 0}
          ≤ ENNReal.ofReal (|a m| * (b m) ^ (i + 2) * CS i) *
            (∑ j ∈ Finset.range (i + 1),
              (Work.CR.Flat.Holder.iDN j g U + Work.CR.Flat.Holder.hSN j α g U)) :=
        (hCS i).2 g hg m
      have h2 := Work.CR.Flat.Holder.le_hSN (f := Work.NN.Final.seeleyTV a b δ g m) i α hx hy hxy
      rw [hxw, hyw] at h2
      have h3 : ENNReal.ofReal (|a m| * (b m) ^ (i + 2) * CS i) *
            (∑ j ∈ Finset.range (i + 1),
              (Work.CR.Flat.Holder.iDN j g U + Work.CR.Flat.Holder.hSN j α g U))
          ≤ ENNReal.ofReal (|a m| * (b m) ^ (i + 2) * CS i * R) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (abs_nonneg _)
          (pow_nonneg (hbmnn m) (i + 2))) (le_of_lt (hCS i).1))]
        exact mul_le_mul' le_rfl (hSumSNV i hi)
      exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
        (pow_nonneg (hbmnn m) (i + 2))) (le_of_lt (hCS i).1)) hR0)).mp (h2.trans (h1.trans h3))
    have hDN : ∀ i ≤ k, Work.NN.Final.gDN i (Work.NN.Final.seeleyEV a b δ g) S
        ≤ ENNReal.ofReal ((AD i + 1) * R) := by
      intro i hi
      refine iSup₂_le fun x hx => ENNReal.ofReal_le_ofReal ?_
      rcases lt_trichotomy x.2 0 with hxneg | hxzero | hxpos
      · have hsm : Summable fun m : ℕ => |a m| * (b m) ^ i * CD i * R :=
          ((hsum i).mul_right (CD i)).mul_right R
        have hsumble : Summable fun m : ℕ =>
            ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x‖ :=
          Summable.of_nonneg_of_le (fun m => norm_nonneg _)
            (fun m => htermDN i hi m x ⟨hx, hxneg⟩) hsm
        have hFsum : iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) x
            = ∑' m, iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x := by
          have hev : Work.NN.Final.seeleyEV a b δ g =ᶠ[𝓝 x] Work.NN.Final.seeleySumV a b δ g :=
            Filter.eventuallyEq_of_mem ((isOpen_lt continuous_snd continuous_const).mem_nhds hxneg)
              (fun z hz => Work.NN.Final.seeleyEV_of_neg a b δ g hz)
          rw [iteratedFDeriv_congr_of_eventuallyEq hev i]
          exact iteratedFDeriv_seeleySumV_of_neg hδ hb hbT hg i hxneg
        calc ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) x‖
            = ‖∑' m, iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x‖ := by rw [hFsum]
          _ ≤ ∑' m, ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x‖ :=
              norm_tsum_le_tsum_norm hsumble
          _ ≤ ∑' m, |a m| * (b m) ^ i * CD i * R :=
              Summable.tsum_le_tsum (fun m => htermDN i hi m x ⟨hx, hxneg⟩) hsumble hsm
          _ = AD i * R := by rw [tsum_mul_right, tsum_mul_right, hAD]
          _ ≤ (AD i + 1) * R := mul_le_mul_of_nonneg_right (by linarith [hADnn i]) hR0
      · have hFdiff : ContDiffAt ℝ (i + 1) (Work.NN.Final.seeleyEV a b δ g) x :=
          (seeleyEV_contDiffOn hδ hb hbT ha hsum hg (i + 1)).contDiffAt (hSopen.mem_nhds hx)
        have h1 : ENNReal.ofReal ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) x‖
            ≤ Work.NN.Final.gDN i (Work.NN.Final.seeleyEV a b δ g) U :=
          ofReal_norm_iteratedFDeriv_le_gDN_halfspace hxzero hFdiff
        have h2 : Work.NN.Final.gDN i (Work.NN.Final.seeleyEV a b δ g) U
            = Work.NN.Final.gDN i g U := by
          refine gDN_eq_of_eventuallyEq (fun z hz => ?_) i
          refine Filter.eventuallyEq_of_mem
            ((isOpen_lt continuous_const continuous_snd).mem_nhds (show (0:ℝ) < z.2 from hz)) ?_
          intro w hw
          exact Work.NN.Final.seeleyEV_of_nonneg a b δ g
            (le_of_lt (show (0:ℝ) < w.2 from hw))
        have h4 : ENNReal.ofReal ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) x‖
            ≤ ENNReal.ofReal R := h1.trans (h2.trans_le (hgDNle i hi))
        have h5 : ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) x‖ ≤ R :=
          (ENNReal.ofReal_le_ofReal_iff hR0).mp h4
        exact h5.trans (le_mul_of_one_le_left hR0 (by linarith [hADnn i]))
      · have hev : Work.NN.Final.seeleyEV a b δ g =ᶠ[𝓝 x] g :=
          Filter.eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_snd).mem_nhds hxpos)
            (fun z hz => Work.NN.Final.seeleyEV_of_nonneg a b δ g (le_of_lt hz))
        rw [iteratedFDeriv_congr_of_eventuallyEq hev i]
        exact (hgpts i hi x (show x ∈ U from hxpos)).trans
          (le_mul_of_one_le_left hR0 (by linarith [hADnn i]))
    have hCU : ∀ i ≤ k, ∀ x y : X × ℝ, x ∈ S → y ∈ S → 0 ≤ x.2 → 0 ≤ y.2 → x ≠ y →
        ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) x
          - iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) y‖ / ‖x - y‖ ^ α ≤ R := by
      intro i hi x y hxS hyS hx0 hy0 hxy
      have hfx : ContDiffAt ℝ (i + 1) (Work.NN.Final.seeleyEV a b δ g) x :=
        (seeleyEV_contDiffOn hδ hb hbT ha hsum hg (i + 1)).contDiffAt (hSopen.mem_nhds hxS)
      have hfy : ContDiffAt ℝ (i + 1) (Work.NN.Final.seeleyEV a b δ g) y :=
        (seeleyEV_contDiffOn hδ hb hbT ha hsum hg (i + 1)).contDiffAt (hSopen.mem_nhds hyS)
      have h1 := ofReal_ratio_le_gSN_halfspace (f := Work.NN.Final.seeleyEV a b δ g) (i := i)
        (α := α) hx0 hy0 hxy hfx hfy
      have h2 : Work.NN.Final.gSN i α (Work.NN.Final.seeleyEV a b δ g) U
          = Work.NN.Final.gSN i α g U := by
        refine gSN_eq_of_eventuallyEq (fun z hz => ?_) i α
        refine Filter.eventuallyEq_of_mem
          ((isOpen_lt continuous_const continuous_snd).mem_nhds (show (0:ℝ) < z.2 from hz)) ?_
        intro w hw
        exact Work.NN.Final.seeleyEV_of_nonneg a b δ g
          (le_of_lt (show (0:ℝ) < w.2 from hw))
      have h3 : Work.NN.Final.gSN i α g U ≤ ENNReal.ofReal R := by
        rw [Work.NN.Final.gSN_eq_hSN hUopen i α g, hofR]
        exact Work.CR.Flat.holderSeminorm_le_holderNorm k α g U hi
      exact (ENNReal.ofReal_le_ofReal_iff hR0).mp (h1.trans (h2.trans_le h3))
    have hAA : ∀ i ≤ k, ∀ x y : X × ℝ, x ∈ {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} →
        y ∈ {p : X × ℝ | -δ < p.2 ∧ p.2 < 0} → x ≠ y →
        ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) x
          - iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) y‖ / ‖x - y‖ ^ α
          ≤ AS i * R := by
      intro i hi x y hx hy hxy
      have hFsum : ∀ z : X × ℝ, z.2 < 0 →
          iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) z
            = ∑' m, iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) z := by
        intro z hz
        have hev : Work.NN.Final.seeleyEV a b δ g =ᶠ[𝓝 z] Work.NN.Final.seeleySumV a b δ g :=
          Filter.eventuallyEq_of_mem ((isOpen_lt continuous_snd continuous_const).mem_nhds hz)
            (fun w hw => Work.NN.Final.seeleyEV_of_neg a b δ g hw)
        rw [iteratedFDeriv_congr_of_eventuallyEq hev i]
        exact iteratedFDeriv_seeleySumV_of_neg hδ hb hbT hg i hz
      have hsm : Summable fun m : ℕ => |a m| * (b m) ^ (i + 2) * CS i * R :=
        ((hsum (i + 2)).mul_right (CS i)).mul_right R
      have hsmx : Summable fun m : ℕ =>
          iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x :=
        Summable.of_norm_bounded (g := fun m : ℕ => |a m| * (b m) ^ i * CD i * R)
          (((hsum i).mul_right (CD i)).mul_right R)
          (fun m => htermDN i hi m x hx)
      have hsmy : Summable fun m : ℕ =>
          iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) y :=
        Summable.of_norm_bounded (g := fun m : ℕ => |a m| * (b m) ^ i * CD i * R)
          (((hsum i).mul_right (CD i)).mul_right R)
          (fun m => htermDN i hi m y hy)
      have hdiff : iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) x
          - iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) y
          = ∑' m, (iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x
              - iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) y) := by
        rw [hFsum x hx.2, hFsum y hy.2, Summable.tsum_sub hsmx hsmy]
      have hdpos : 0 < ‖x - y‖ ^ α :=
        Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
      have hterm : ∀ m : ℕ, ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x
            - iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) y‖
          ≤ |a m| * (b m) ^ (i + 2) * CS i * R * ‖x - y‖ ^ α := by
        intro m
        have h1 := htermSN i hi m x y hx hy hxy
        calc ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x
              - iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) y‖
            = (‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x
                - iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) y‖ / ‖x - y‖ ^ α)
                * ‖x - y‖ ^ α := (div_mul_cancel₀ _ (ne_of_gt hdpos)).symm
          _ ≤ (|a m| * (b m) ^ (i + 2) * CS i * R) * ‖x - y‖ ^ α :=
              mul_le_mul_of_nonneg_right h1 hdpos.le
      have hsmt : Summable fun m : ℕ => ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x
          - iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) y‖ :=
        Summable.of_nonneg_of_le (fun m => norm_nonneg _) hterm
          (hsm.mul_right (‖x - y‖ ^ α))
      have hmain : ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) x
          - iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) y‖
          ≤ (AS i * R) * ‖x - y‖ ^ α := by
        calc ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) x
              - iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) y‖
            = ‖∑' m, (iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x
                - iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) y)‖ := by rw [hdiff]
          _ ≤ ∑' m, ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) x
                - iteratedFDeriv ℝ i (Work.NN.Final.seeleyTV a b δ g m) y‖ :=
              norm_tsum_le_tsum_norm hsmt
          _ ≤ ∑' m, |a m| * (b m) ^ (i + 2) * CS i * R * ‖x - y‖ ^ α :=
              Summable.tsum_le_tsum hterm hsmt (hsm.mul_right _)
          _ = AS i * R * ‖x - y‖ ^ α := by
              rw [tsum_mul_right, tsum_mul_right, tsum_mul_right, hAS]
      exact (div_le_iff₀ hdpos).mpr hmain
    have hCL : ∀ i ≤ k, ∀ x y : X × ℝ, -δ < x.2 → x.2 ≤ 0 → -δ < y.2 → y.2 ≤ 0 → x ≠ y →
        ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) x
          - iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) y‖ / ‖x - y‖ ^ α
          ≤ AS i * R := by
      intro i hi x y hxδ hx0 hyδ hy0 hxy
      refine ratio_le_closed_lower_of_le_open_lower (f := Work.NN.Final.seeleyEV a b δ g)
        (α := α) (δ := δ) (K := AS i * R) ?_ ?_ hxδ hx0 hyδ hy0 hxy
      · intro z hzδ hz0
        exact (seeleyEV_contDiffOn hδ hb hbT ha hsum hg (i + 1)).contDiffAt
          (hSopen.mem_nhds (show z ∈ S from hzδ))
      · intro u v huδ hu0 hvδ hv0 huv
        exact hAA i hi u v ⟨huδ, hu0⟩ ⟨hvδ, hv0⟩ huv
    have hmix : ∀ i ≤ k, ∀ x y : X × ℝ, x ∈ S → y ∈ S →
        (0 < x.2 ∧ y.2 < 0 ∨ 0 < y.2 ∧ x.2 < 0) → x ≠ y →
        ‖iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) x
          - iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) y‖ / ‖x - y‖ ^ α
          ≤ (1 + AS i) * R := by
      intro i hi x y hxS hyS hmc hxy
      let D : X × ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin i => X × ℝ) ℂ :=
        fun p => iteratedFDeriv ℝ i (Work.NN.Final.seeleyEV a b δ g) p
      change ‖D x - D y‖ / ‖x - y‖ ^ α ≤ (1 + AS i) * R
      rcases hmc with ⟨hxp, hyn⟩ | ⟨hyp, hxn⟩
      · set w : X × ℝ := (x.1, 0) with hw
        have hw2 : w.2 = (0:ℝ) := by rw [hw]
        have hwδ : -δ < w.2 := by rw [hw2]; linarith [hδ]
        have hw0 : (0:ℝ) ≤ w.2 := by rw [hw2]
        have hwS : w ∈ S := hwδ
        have hwx : x ≠ w := by
          intro h
          have h2 := congrArg Prod.snd h
          rw [hw] at h2
          simp at h2
          linarith [hxp]
        have hwy : w ≠ y := by
          intro h
          have h2 := congrArg Prod.snd h
          rw [hw] at h2
          simp at h2
          linarith [hyn]
        have h1 : ‖D x - D w‖ ≤ R * ‖x - w‖ ^ α := by
          have hcw := hCU i hi x w hxS hwS (le_of_lt hxp) hw0 hwx
          have hpos : 0 < ‖x - w‖ ^ α :=
            Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hwx)) α
          calc ‖D x - D w‖ = (‖D x - D w‖ / ‖x - w‖ ^ α) * ‖x - w‖ ^ α :=
                (div_mul_cancel₀ _ (ne_of_gt hpos)).symm
            _ ≤ R * ‖x - w‖ ^ α := mul_le_mul_of_nonneg_right hcw hpos.le
        have h3 : ‖D w - D y‖ ≤ (AS i * R) * ‖w - y‖ ^ α := by
          have hcw := hCL i hi w y hwδ hw0 (show -δ < y.2 from hyS) (le_of_lt hyn) hwy
          have hpos : 0 < ‖w - y‖ ^ α :=
            Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hwy)) α
          calc ‖D w - D y‖ = (‖D w - D y‖ / ‖w - y‖ ^ α) * ‖w - y‖ ^ α :=
                (div_mul_cancel₀ _ (ne_of_gt hpos)).symm
            _ ≤ (AS i * R) * ‖w - y‖ ^ α := mul_le_mul_of_nonneg_right hcw hpos.le
        have hd1 := norm_sub_fst_zero_le (X := X) (p := x) (q := y) hxp hyn
        have hd2 := norm_sub_fst_zero_le' (X := X) (p := x) (q := y) hxp hyn
        have hp1 : ‖x - w‖ ^ α ≤ ‖x - y‖ ^ α := Real.rpow_le_rpow (norm_nonneg _) hd1 hα0.le
        have hp2 : ‖w - y‖ ^ α ≤ ‖x - y‖ ^ α := Real.rpow_le_rpow (norm_nonneg _) hd2 hα0.le
        have hdpos : 0 < ‖x - y‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α
        refine (div_le_iff₀ hdpos).mpr ?_
        calc ‖D x - D y‖
            ≤ ‖D x - D w‖ + ‖D w - D y‖ := by
              rw [show D x - D y = (D x - D w) + (D w - D y) from by abel]
              exact norm_add_le _ _
          _ ≤ R * ‖x - w‖ ^ α + (AS i * R) * ‖w - y‖ ^ α := add_le_add h1 h3
          _ ≤ R * ‖x - y‖ ^ α + (AS i * R) * ‖x - y‖ ^ α :=
              add_le_add (mul_le_mul_of_nonneg_left hp1 hR0)
                (mul_le_mul_of_nonneg_left hp2 (mul_nonneg (hASnn i) hR0))
          _ = (1 + AS i) * R * ‖x - y‖ ^ α := by ring
      · set w : X × ℝ := (y.1, 0) with hw
        have hw2 : w.2 = (0:ℝ) := by rw [hw]
        have hwδ : -δ < w.2 := by rw [hw2]; linarith [hδ]
        have hw0 : (0:ℝ) ≤ w.2 := by rw [hw2]
        have hwS : w ∈ S := hwδ
        have hwy : y ≠ w := by
          intro h
          have h2 := congrArg Prod.snd h
          rw [hw] at h2
          simp at h2
          linarith [hyp]
        have hwx : w ≠ x := by
          intro h
          have h2 := congrArg Prod.snd h
          rw [hw] at h2
          simp at h2
          linarith [hxn]
        have h1 : ‖D w - D x‖ ≤ (AS i * R) * ‖w - x‖ ^ α := by
          have hcw := hCL i hi w x hwδ hw0 (show -δ < x.2 from hxS) (le_of_lt hxn) hwx
          have hpos : 0 < ‖w - x‖ ^ α :=
            Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hwx)) α
          calc ‖D w - D x‖ = (‖D w - D x‖ / ‖w - x‖ ^ α) * ‖w - x‖ ^ α :=
                (div_mul_cancel₀ _ (ne_of_gt hpos)).symm
            _ ≤ (AS i * R) * ‖w - x‖ ^ α := mul_le_mul_of_nonneg_right hcw hpos.le
        have h3 : ‖D y - D w‖ ≤ R * ‖y - w‖ ^ α := by
          have hcw := hCU i hi y w hyS hwS (le_of_lt hyp) hw0 hwy
          have hpos : 0 < ‖y - w‖ ^ α :=
            Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hwy)) α
          calc ‖D y - D w‖ = (‖D y - D w‖ / ‖y - w‖ ^ α) * ‖y - w‖ ^ α :=
                (div_mul_cancel₀ _ (ne_of_gt hpos)).symm
            _ ≤ R * ‖y - w‖ ^ α := mul_le_mul_of_nonneg_right hcw hpos.le
        have hd1 := norm_sub_fst_zero_le (X := X) (p := y) (q := x) hyp hxn
        have hd2 := norm_sub_fst_zero_le' (X := X) (p := y) (q := x) hyp hxn
        have hp1 : ‖w - x‖ ^ α ≤ ‖y - x‖ ^ α := Real.rpow_le_rpow (norm_nonneg _) hd2 hα0.le
        have hp2 : ‖y - w‖ ^ α ≤ ‖y - x‖ ^ α := Real.rpow_le_rpow (norm_nonneg _) hd1 hα0.le
        have hgoal : ‖D x - D y‖ / ‖x - y‖ ^ α = ‖D x - D y‖ / ‖y - x‖ ^ α := by
          rw [norm_sub_rev x y]
        rw [hgoal]
        have hdpos : 0 < ‖y - x‖ ^ α :=
          Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))) α
        refine (div_le_iff₀ hdpos).mpr ?_
        calc ‖D x - D y‖
            ≤ ‖D x - D w‖ + ‖D w - D y‖ := by
              rw [show D x - D y = (D x - D w) + (D w - D y) from by abel]
              exact norm_add_le _ _
          _ = ‖D w - D x‖ + ‖D y - D w‖ := by
              rw [norm_sub_rev (D x) (D w), norm_sub_rev (D w) (D y)]
          _ ≤ (AS i * R) * ‖w - x‖ ^ α + R * ‖y - w‖ ^ α := add_le_add h1 h3
          _ ≤ (AS i * R) * ‖y - x‖ ^ α + R * ‖y - x‖ ^ α :=
              add_le_add (mul_le_mul_of_nonneg_left hp1 (mul_nonneg (hASnn i) hR0))
                (mul_le_mul_of_nonneg_left hp2 hR0)
          _ = (1 + AS i) * R * ‖y - x‖ ^ α := by ring
    have hSN : ∀ i ≤ k, Work.NN.Final.gSN i α (Work.NN.Final.seeleyEV a b δ g) S
        ≤ ENNReal.ofReal ((AS i + 2) * R) := by
      intro i hi
      have h2R : R ≤ (AS i + 2) * R := le_mul_of_one_le_left hR0 (by linarith [hASnn i])
      have h2A : AS i * R ≤ (AS i + 2) * R :=
        mul_le_mul_of_nonneg_right (by linarith) hR0
      have h2B : (1 + AS i) * R ≤ (AS i + 2) * R :=
        mul_le_mul_of_nonneg_right (by linarith) hR0
      refine iSup₂_le fun x hx => iSup₂_le fun y hy =>
        iSup_le fun hxy => ENNReal.ofReal_le_ofReal ?_
      rcases lt_trichotomy x.2 0 with hxn | hxz | hxp
      · rcases lt_trichotomy y.2 0 with hyn | hyz | hyp
        · exact (hCL i hi x y hx (le_of_lt hxn) hy (le_of_lt hyn) hxy).trans h2A
        · exact (hCL i hi x y hx (le_of_lt hxn) hy (le_of_eq hyz) hxy).trans h2A
        · exact (hmix i hi x y hx hy (Or.inr ⟨hyp, hxn⟩) hxy).trans h2B
      · rcases lt_trichotomy y.2 0 with hyn | hyz | hyp
        · exact (hCL i hi x y hx (le_of_eq hxz) hy (le_of_lt hyn) hxy).trans h2A
        · exact (hCL i hi x y hx (le_of_eq hxz) hy (le_of_eq hyz) hxy).trans h2A
        · exact (hCU i hi x y hx hy (le_of_eq hxz.symm) (le_of_lt hyp) hxy).trans h2R
      · rcases lt_trichotomy y.2 0 with hyn | hyz | hyp
        · exact (hmix i hi x y hx hy (Or.inl ⟨hxp, hyn⟩) hxy).trans h2B
        · exact (hCU i hi x y hx hy (le_of_lt hxp) (le_of_eq hyz.symm) hxy).trans h2R
        · exact (hCU i hi x y hx hy (le_of_lt hxp) (le_of_lt hyp) hxy).trans h2R
    have hFsplit : Work.CR.Flat.holderNorm k α (Work.NN.Final.seeleyEV a b δ g) S
        = ∑ i ∈ Finset.range (k + 1),
            (Work.NN.Final.gDN i (Work.NN.Final.seeleyEV a b δ g) S
              + Work.NN.Final.gSN i α (Work.NN.Final.seeleyEV a b δ g) S) := by
      unfold Work.CR.Flat.holderNorm
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      · exact (Work.CR.Flat.Holder.iDN_complex_eq i (Work.NN.Final.seeleyEV a b δ g) S).symm.trans
          (Work.NN.Final.gDN_eq_iDN hSopen i (Work.NN.Final.seeleyEV a b δ g)).symm
      · exact (Work.CR.Flat.Holder.hSN_complex_eq i α (Work.NN.Final.seeleyEV a b δ g) S).symm.trans
          (Work.NN.Final.gSN_eq_hSN hSopen i α (Work.NN.Final.seeleyEV a b δ g)).symm
    rw [hFsplit]
    calc (∑ i ∈ Finset.range (k + 1),
            (Work.NN.Final.gDN i (Work.NN.Final.seeleyEV a b δ g) S
              + Work.NN.Final.gSN i α (Work.NN.Final.seeleyEV a b δ g) S))
        ≤ ∑ i ∈ Finset.range (k + 1),
            (ENNReal.ofReal ((AD i + 1) * R) + ENNReal.ofReal ((AS i + 2) * R)) :=
          Finset.sum_le_sum fun i hi' =>
            add_le_add (hDN i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')))
              (hSN i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi')))
      _ = (∑ i ∈ Finset.range (k + 1),
            (ENNReal.ofReal (AD i + 1) + ENNReal.ofReal (AS i + 2))) * ENNReal.ofReal R := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ENNReal.ofReal_mul (by linarith [hADnn i]),
            ENNReal.ofReal_mul (by linarith [hASnn i]), add_mul]
      _ ≤ ENNReal.ofReal (Cfun k) * Work.CR.Flat.holderNorm k α g U := by
          rw [← hofR]
          refine mul_le_mul' ?_ le_rfl
          have hsum_le : (∑ i ∈ Finset.range (k + 1),
                (ENNReal.ofReal (AD i + 1) + ENNReal.ofReal (AS i + 2)))
              ≤ ENNReal.ofReal (Cfun k) := by
            have h1 : (∑ i ∈ Finset.range (k + 1),
                  (ENNReal.ofReal (AD i + 1) + ENNReal.ofReal (AS i + 2)))
                = ENNReal.ofReal ((∑ i ∈ Finset.range (k + 1), (AD i + 1))
                    + ∑ i ∈ Finset.range (k + 1), (AS i + 2)) := by
              rw [Finset.sum_add_distrib,
                ← ENNReal.ofReal_sum_of_nonneg (f := fun i => AD i + 1)
                  (fun i _ => by linarith [hADnn i]),
                ← ENNReal.ofReal_sum_of_nonneg (f := fun i => AS i + 2)
                  (fun i _ => by linarith [hASnn i]),
                ← ENNReal.ofReal_add
                  (Finset.sum_nonneg fun i _ => by linarith [hADnn i])
                  (Finset.sum_nonneg fun i _ => by linarith [hASnn i])]
            rw [h1]
            change ENNReal.ofReal ((∑ i ∈ Finset.range (k + 1), (AD i + 1))
                + ∑ i ∈ Finset.range (k + 1), (AS i + 2))
              ≤ ENNReal.ofReal ((∑ i ∈ Finset.range (k + 1), (AD i + 1 + (AS i + 2))) + 1)
            have h2 : (∑ i ∈ Finset.range (k + 1), (AD i + 1 + (AS i + 2)))
                = (∑ i ∈ Finset.range (k + 1), (AD i + 1))
                  + ∑ i ∈ Finset.range (k + 1), (AS i + 2) := Finset.sum_add_distrib
            rw [h2]
            refine ENNReal.ofReal_le_ofReal ?_
            linarith
          exact hsum_le

end Work.NN.Seeley
