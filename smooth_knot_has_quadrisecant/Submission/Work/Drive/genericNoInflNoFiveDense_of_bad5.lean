import Mathlib
import Submission.Work.Drive.fiveCollinearBadSet
import Submission.Work.Drive.quadrisecantSpreadDefs
import Submission.Work.Drive.tangencyBadSet
import Submission.Work.Drive.exists_close_transverse_noInflection
import Submission.Work.Drive.noFiveCollinear_bad_interior_empty
import Submission.Work.Drive.patchStrata
import Submission.Work.Drive.genericNoInflDense

/-!
# `Work.Drive.genericNoInflNoFiveDense_of_bad5`

The density of the *five-collinear-free* generic approximants, reduced to the bad-set lemma
`Work.Drive.bad5`: if for every smooth knot `r`, every coefficient ball `Kv r₀` all of whose
elements are knots, and every separation scale `k`, the set `bad5 r r₀ k` of coefficients admitting
five collinear points at pairwise `1/(k+1)`-separated parameters has empty interior, then

  `Work.Drive.GenericNoInflNoFiveDense`

holds: every smooth knot has arbitrarily `C¹`-close approximants that are in transverse general
position, have no inflection points and have no five collinear points.

The proof is the *combined Baire* assembly: the bad-set argument of
`Work.Drive.exists_close_transverse_noInflection` (`badABC`, `badPsi`) is run with the extra
countable family `k ↦ bad5 r₁ r₀ k` added to the intersection.  The only two facts needed about
`bad5` are that it is *closed* (so that its complement is open and `dense_iInter_of_isOpen`
applies) and that its interior is empty (which is the hypothesis `h5`).  The passage from
"`c` avoids every `bad5 r r₀ k`" to `NoFiveCollinear (pertV r c)` is `noFiveCollinear_of_not_bad5`
below: a five-tuple of distinct circle parameters is `1/(k+1)`-separated for some `k`, and
`knotMap_coe` turns the collinearity of the images into the line condition of `bad5`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## The five-point line predicate is closed -/

/-- Five points of `Space` are contained in an affine line (a degenerate line, i.e. a single
point, being allowed: the direction is required to be non-zero but the parameters may all
vanish). -/
def fiveOnLine (P : Fin 5 → Space) : Prop :=
  ∃ p v : Space, v ≠ 0 ∧ ∀ i : Fin 5, ∃ t : ℝ, P i = p + t • v

/-- **The five-point line predicate is closed**, via the equivalent "all differences from one
point are parallel" formulation. -/
lemma isClosed_fiveOnLine : IsClosed {P : Fin 5 → Space | fiveOnLine P} := by
  have hset : {P : Fin 5 → Space | fiveOnLine P} =
      ⋂ i : Fin 5, ⋂ j : Fin 5, ⋂ l : Fin 5,
        {P : Fin 5 → Space | cross3 (P j - P i) (P l - P i) = 0} := by
    ext P
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨p, v, hv, ht⟩ i j l
      obtain ⟨tj, htj⟩ := ht j
      obtain ⟨tl, htl⟩ := ht l
      obtain ⟨ti, hti⟩ := ht i
      have h1 : P j - P i = (tj - ti) • v := by rw [htj, hti]; module
      have h2 : P l - P i = (tl - ti) • v := by rw [htl, hti]; module
      rw [h1, h2, cross3_smul_left, cross3_smul_right, cross3_self]
      simp
    · intro h
      by_cases h0 : ∀ i : Fin 5, P i = P 0
      · obtain ⟨v, hv⟩ := exists_ne (0 : Space)
        refine ⟨P 0, v, hv, fun i => ⟨(0 : ℝ), ?_⟩⟩
        rw [h0 i]; simp
      · push_neg at h0
        obtain ⟨i₀, hi₀⟩ := h0
        refine ⟨P 0, P i₀ - P 0, sub_ne_zero.mpr hi₀, fun l => ?_⟩
        have hcross : cross3 (P i₀ - P 0) (P l - P 0) = 0 := h 0 i₀ l
        rcases (cross3_eq_zero_iff_smul_local _ _).mp hcross with hzero | ⟨t, ht⟩
        · exact absurd hzero (sub_ne_zero.mpr hi₀)
        · exact ⟨t, by rw [← ht]; module⟩
  rw [hset]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun l => ?_
  have h1 : Continuous (fun P : Fin 5 → Space => P j - P i) :=
    (continuous_apply j).sub (continuous_apply i)
  have h2 : Continuous (fun P : Fin 5 → Space => P l - P i) :=
    (continuous_apply l).sub (continuous_apply i)
  exact isClosed_eq
    ((Commons.Analysis.CrossProduct.cross3_contDiff.continuous).comp (h1.prodMk h2))
    continuous_const

/-- **The bad set of five collinear points is closed.**  It is the projection (onto the coefficient
space) of the closed subset of the compact set `Kv r₀ ×ˢ K5 k` on which the (continuous) value map
takes a value in the closed set of collinear configurations. -/
theorem isClosed_bad5 {r : ℝ → Space} (hr : IsSmoothKnot r) (r₀ : ℝ) (k : ℕ) :
    IsClosed (bad5 r r₀ k) := by
  have hcont : Continuous (valMap r) := (contDiff_valMap hr).continuous
  have himg : Prod.fst '' ((Kv r₀ ×ˢ K5 k) ∩ (valMap r) ⁻¹' {P : Fin 5 → Space | fiveOnLine P})
      = bad5 r r₀ k := by
    ext c
    constructor
    · rintro ⟨p, ⟨⟨hp1, hp2⟩, hp3⟩, rfl⟩
      obtain ⟨hw1, hw2⟩ := mem_K5.mp hp2
      exact ⟨hp1, p.2, hw1, hw2, hp3⟩
    · rintro ⟨hc, w, hw1, hw2, hline⟩
      exact ⟨(c, w), ⟨⟨hc, mem_K5.mpr ⟨hw1, hw2⟩⟩, hline⟩, rfl⟩
  rw [← himg]
  have hcomp : IsCompact ((Kv r₀ ×ˢ K5 k) ∩ (valMap r) ⁻¹' {P : Fin 5 → Space | fiveOnLine P}) :=
    ((isCompact_Kv r₀).prod (isCompact_K5 k)).inter_right (isClosed_fiveOnLine.preimage hcont)
  exact (hcomp.image continuous_fst).isClosed

/-! ## A generic Baire step -/

/-- **The Baire step.**  If every member of a countable family `bad i` of *closed* subsets of
`Coeff` has empty interior and is contained in the coefficient ball `Kv r₀`, then the ball contains
coefficients avoiding the whole family. -/
theorem exists_coeff_avoiding {ι : Type*} [Countable ι] {r₀ : ℝ} (hr₀ : 0 < r₀)
    (bad : ι → Set Coeff) (hclosed : ∀ i, IsClosed (bad i))
    (hempty : ∀ i, interior (bad i) = ∅) :
    ∃ c ∈ interior (Kv r₀), ∀ i, c ∉ bad i := by
  have hopen : ∀ i, IsOpen ((bad i)ᶜ) := fun i => (hclosed i).isOpen_compl
  have hdense : ∀ i, Dense ((bad i)ᶜ) := fun i => interior_eq_empty_iff_dense_compl.mp (hempty i)
  have hBaire : Dense (⋂ i, (bad i)ᶜ) := dense_iInter_of_isOpen hopen hdense
  have hUne : (interior (Kv r₀)).Nonempty := by
    refine ⟨0, ?_⟩
    rw [Kv]
    exact interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      (Metric.mem_ball_self hr₀)
  obtain ⟨c, hcmem, hcU⟩ := hBaire.exists_mem_open isOpen_interior hUne
  exact ⟨c, hcU, fun i hi => Set.mem_iInter.mp hcmem i hi⟩

/-! ## A finite uniform separation scale -/

/-- **A finite family of positive reals is bounded below by `1/(k+1)` for some `k`.** -/
lemma exists_div_succ_le_finset {ι : Type*} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ k : ℕ, ∀ i, (1 : ℝ) / (k + 1) ≤ f i := by
  classical
  have h : ∀ s : Finset ι, (∀ i ∈ s, 0 < f i) → ∃ k : ℕ, ∀ i ∈ s, (1 : ℝ) / (k + 1) ≤ f i := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      exact ⟨0, by simp⟩
    · intro a s has ih hs
      obtain ⟨k₁, hk₁⟩ := ih fun i hi => hs i (Finset.mem_insert_of_mem hi)
      obtain ⟨k₂, hk₂⟩ := exists_div_succ_le (hs a (Finset.mem_insert_self a s))
      refine ⟨max k₁ k₂, ?_⟩
      have hk₁' : (1 : ℝ) / ((max k₁ k₂ : ℕ) + 1) ≤ (1 : ℝ) / (k₁ + 1) :=
        one_div_le_one_div_of_le (by positivity) (by
          have : k₁ + 1 ≤ max k₁ k₂ + 1 := by omega
          exact_mod_cast this)
      have hk₂' : (1 : ℝ) / ((max k₁ k₂ : ℕ) + 1) ≤ (1 : ℝ) / (k₂ + 1) :=
        one_div_le_one_div_of_le (by positivity) (by
          have : k₂ + 1 ≤ max k₁ k₂ + 1 := by omega
          exact_mod_cast this)
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hk₂'.trans hk₂
      · exact hk₁'.trans (hk₁ i hi)
  obtain ⟨k, hk⟩ := h Finset.univ (fun i _ => hf i)
  exact ⟨k, fun i => hk i (Finset.mem_univ i)⟩

/-- **The passage from the bad set to the geometric condition.**  If `c` lies in no `bad5 r r₀ k`,
then the perturbed curve `pertV r c` has no five collinear points: a five-tuple of distinct circle
parameters is `1/(k+1)`-separated for some `k`, and the representatives of a period turn the
collinearity of the knot images into the line condition defining `bad5`. -/
theorem noFiveCollinear_of_not_bad5 {r : ℝ → Space} {r₀ : ℝ} {c : Coeff} (hc : c ∈ Kv r₀)
    (h : ∀ k : ℕ, c ∉ bad5 r r₀ k) : NoFiveCollinear (pertV r c) := by
  classical
  rintro ⟨cc, hinj, p, v, hv, hline⟩
  choose w hwmem hweq using fun i : Fin 5 => AddCircle.eq_coe_Ico (cc i)
  -- the images of the chosen representatives are the knot images of the `cc i`
  have hval : ∀ i : Fin 5, pertV r c (w i) = p + (Classical.choose (hline i)) • v := by
    intro i
    have h1 : knotMap (pertV r c) (cc i) = pertV r c (w i) := by
      rw [← hweq i]
      exact knotMap_coe _ (hwmem i)
    rw [← h1]
    exact (hline i).choose_spec
  -- pairwise circular separation of the representatives is positive
  have hsep_pos : ∀ i j : Fin 5, i ≠ j → 0 < csep (w i) (w j) := by
    intro i j hij
    have hne : (w i : AddCircle period) ≠ (w j : AddCircle period) := by
      rw [hweq i, hweq j]
      exact fun hcc => hij (hinj hcc)
    have hwij : w i ≠ w j := fun hwij => hne (by rw [hwij])
    have hlt : |w i - w j| < 2 * Real.pi := by
      have hi := hwmem i
      have hj := hwmem j
      have hi2 : w i < 2 * Real.pi := by simpa [period] using hi.2
      have hj2 : w j < 2 * Real.pi := by simpa [period] using hj.2
      rw [abs_lt]
      exact ⟨by linarith [hi.1, hj2], by linarith [hi2, hj.1]⟩
    have hpos : 0 < min |w i - w j| (2 * Real.pi - |w i - w j|) := by
      rw [lt_min_iff]
      exact ⟨abs_pos.mpr (sub_ne_zero.mpr hwij), by linarith⟩
    simpa [csep] using hpos
  -- the uniform separation scale
  obtain ⟨k, hk⟩ := exists_div_succ_le_finset
    (fun q : Fin 5 × Fin 5 => if q.1 = q.2 then 1 else csep (w q.1) (w q.2))
    (fun q => by
      by_cases hq : q.1 = q.2
      · simp [if_pos hq]
      · rw [if_neg hq]
        exact hsep_pos q.1 q.2 hq)
  refine h k ?_
  have hb : ∀ i : Fin 5, w i ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := fun i =>
    ⟨(hwmem i).1, le_of_lt (by simpa [period] using (hwmem i).2)⟩
  have hs : ∀ i j : Fin 5, i ≠ j → (1 : ℝ) / (k + 1) ≤ csep (w i) (w j) := fun i j hij => by
    have hkij := hk (i, j)
    rwa [if_neg (by simpa using hij)] at hkij
  exact ⟨hc, w, hb, hs, p, v, hv, fun i => ⟨_, hval i⟩⟩

/-! ## The combined Baire family -/

/-- The index type of the three bad families: the two linear/parallel strata and the
five-collinear bad sets. -/
abbrev BadIdx5 := ((ℕ × Fin 3) ⊕ (ℕ × ℕ)) ⊕ ℕ

/-- The combined bad family of the density argument. -/
def badFam5 (r : ℝ → Space) (r₀ : ℝ) : BadIdx5 → Set Coeff
  | Sum.inl (Sum.inl j) => badABC r r₀ j
  | Sum.inl (Sum.inr j) => badPsi r r₀ j
  | Sum.inr k => bad5 r r₀ k

theorem exists_close_generic_noFive_of_bad5
    (h5 : ∀ (r : ℝ → Space), IsSmoothKnot r → ∀ r₀ : ℝ, 0 < r₀ →
      (∀ c ∈ Kv r₀, IsSmoothKnot (pertV r c)) → ∀ k : ℕ, interior (bad5 r r₀ k) = ∅)
    {r : ℝ → Space} (hr : IsSmoothKnot r) (ε : ℝ) (hε : 0 < ε) :
    ∃ r' : ℝ → Space, IsSmoothKnot r' ∧ TorusGeneralPositionTransverse r' ∧
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) ∧ NoFiveCollinear r' ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε := by
  classical
  -- step 1: first remove the inflections
  obtain ⟨r₁, h₁, hnoinfl₁, hclose₁⟩ := exists_close_nonzero_curvature hr (ε/2) (by linarith)
  have hnoinfl₁' : ∀ t : ℝ, cross3 (velocity r₁ t) (deriv (velocity r₁) t) ≠ 0 :=
    fun t => (linearIndependent_pair_iff_cross3_ne_zero _ _).mp (hnoinfl₁ t)
  -- step 2: nonvanishing curvature is preserved on a ball
  obtain ⟨ρ, hρpos, hρ⟩ := exists_curvPreserve_bound h₁ hnoinfl₁'
  -- step 3: the smallness constants
  obtain ⟨ε₀, hε₀pos, hsm⟩ := smallCorrectionKnot h₁
  set Kc : ℝ := max ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ 1 with hKcdef
  have hKcpos : 0 < Kc := lt_of_lt_of_le one_pos (le_max_right _ _)
  set r₀ : ℝ := min (min (ρ/2) (ε₀/(100*Kc))) (ε/(100*Kc)) with hr₀def
  have hr₀pos : 0 < r₀ := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hr₀leρ : r₀ ≤ ρ := by
    have h2 : r₀ ≤ ρ/2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hr₀leε : r₀ ≤ ε/(100*Kc) := min_le_right _ _
  have hr₀leε₀ : r₀ ≤ ε₀/(100*Kc) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hbound : ∀ c ∈ Kv r₀, ‖eCoeff c‖ ≤ Kc * r₀ := by
    intro c hc
    have hcn : ‖c‖ ≤ r₀ := by rw [Kv, Metric.mem_closedBall, dist_zero_right] at hc; exact hc
    have hop : ‖eCoeff c‖ ≤ ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ * ‖c‖ :=
      ContinuousLinearMap.le_opNorm (eCoeff : Coeff →L[ℝ] (Fin 9 → Space)) c
    have hkey : ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ * ‖c‖ ≤ Kc * r₀ :=
      mul_le_mul (le_max_left _ _) hcn (norm_nonneg c)
        (le_trans (norm_nonneg _) (le_max_left _ _))
    linarith
  have hS : ∀ c ∈ Kv r₀, IsSmoothKnot (pertV r₁ c) := by
    intro c hc
    refine isSmoothKnot_pertV h₁ hε₀pos hsm ?_
    have h1 := hbound c hc
    have h2 : Kc * r₀ ≤ ε₀/100 := by
      have := mul_le_mul_of_nonneg_left hr₀leε₀ hKcpos.le
      rwa [show Kc * (ε₀/(100*Kc)) = ε₀/100 from by field_simp] at this
    linarith
  -- step 4: the combined Baire step (the three bad families)
  have hclosed : ∀ i : BadIdx5, IsClosed (badFam5 r₁ r₀ i) := by
    rintro ((j | j) | k)
    · exact isClosed_badSet (isCompact_tripleSet j.1) (contDiff_stratABC h₁ j.2).continuous r₀
    · exact isClosed_badSet (isCompact_Kn j.1 (j.2 : ℝ)) (contDiff_stratPsi h₁).continuous r₀
    · exact isClosed_bad5 h₁ r₀ k
  have hempty : ∀ i : BadIdx5, interior (badFam5 r₁ r₀ i) = ∅ := by
    rintro ((j | j) | k)
    · exact badABC_empty_interior h₁ hS jetSurj_holds j
    · exact badPsi_empty_interior h₁ hS jetSurj_holds j
    · exact h5 r₁ h₁ r₀ hr₀pos hS k
  obtain ⟨c, hcU, hgood⟩ := exists_coeff_avoiding hr₀pos (badFam5 r₁ r₀) hclosed hempty
  have hcKv : c ∈ Kv r₀ := interior_subset hcU
  have hgoodABC : ∀ (j : Fin 3) (k : ℕ) (w : ℝ × ℝ × ℝ),
      w ∈ tripleSet k → stratABC r₁ j (c, w) ≠ 0 := by
    intro j k w hw hzero
    exact hgood (Sum.inl (Sum.inl (k, j))) ⟨hcKv, w, hw, hzero⟩
  have hgoodPsi : ∀ (k L : ℕ) (w : Cfg), w ∈ Kn k L → stratPsi r₁ (c, w) ≠ 0 := by
    intro k L w hw hzero
    exact hgood (Sum.inl (Sum.inr (k, L))) ⟨hcKv, w, hw, hzero⟩
  have hgood5 : ∀ k : ℕ, c ∉ bad5 r₁ r₀ k := fun k => hgood (Sum.inr k)
  refine ⟨pertV r₁ c, hS c hcKv, ?_, ?_, ?_, ?_⟩
  · -- torus transverse general position, from the pointwise condition
    refine torusGeneralPositionTransverse_of_pointwise ?_
    intro a b m ha hb hm hcol hdist
    have haI : a ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
      ⟨ha.1, le_of_lt (by simpa [period] using ha.2)⟩
    have hbI : b ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
      ⟨hb.1, le_of_lt (by simpa [period] using hb.2)⟩
    have hmI : m ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
      ⟨hm.1, le_of_lt (by simpa [period] using hm.2)⟩
    have ha2 : a < 2 * Real.pi := by simpa [period] using ha.2
    have hb2 : b < 2 * Real.pi := by simpa [period] using hb.2
    have hm2 : m < 2 * Real.pi := by simpa [period] using hm.2
    have hab : a ≠ b := fun h => hdist.1 (by rw [h, sub_self])
    have ham : a ≠ m := fun h => hdist.2.1 (by rw [h, sub_self])
    have hbm : b ≠ m := fun h => hdist.2.2 (by rw [h, sub_self])
    have hcsep1 : 0 < csep a b := by
      have hlt : |a - b| < 2 * Real.pi := by
        rw [abs_lt]; exact ⟨by linarith [haI.1, hb2], by linarith [ha2, hbI.1]⟩
      exact lt_min (abs_pos.mpr (sub_ne_zero.mpr hab)) (sub_pos.mpr hlt)
    have hcsep2 : 0 < csep a m := by
      have hlt : |a - m| < 2 * Real.pi := by
        rw [abs_lt]; exact ⟨by linarith [haI.1, hm2], by linarith [ha2, hmI.1]⟩
      exact lt_min (abs_pos.mpr (sub_ne_zero.mpr ham)) (sub_pos.mpr hlt)
    have hcsep3 : 0 < csep b m := by
      have hlt : |b - m| < 2 * Real.pi := by
        rw [abs_lt]; exact ⟨by linarith [hbI.1, hm2], by linarith [hb2, hmI.1]⟩
      exact lt_min (abs_pos.mpr (sub_ne_zero.mpr hbm)) (sub_pos.mpr hlt)
    obtain ⟨k, hk⟩ := exists_div_succ_le (lt_min (lt_min hcsep1 hcsep2) hcsep3)
    have hk1 : (1:ℝ)/(k+1) ≤ csep a b :=
      hk.trans (le_trans (min_le_left _ _) (min_le_left _ _))
    have hk2 : (1:ℝ)/(k+1) ≤ csep a m :=
      hk.trans (le_trans (min_le_left _ _) (min_le_right _ _))
    have hk3 : (1:ℝ)/(k+1) ≤ csep b m := hk.trans (min_le_right _ _)
    have hw : (a, b, m) ∈ tripleSet k := ⟨haI, hbI, hmI, hk1, hk2, hk3⟩
    have hA := hgoodABC 0 k (a, b, m) hw
    have hB := hgoodABC 1 k (a, b, m) hw
    have hM := hgoodABC 2 k (a, b, m) hw
    -- the three tangent–chord vectors are nonzero
    have hyA : cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      intro hzero
      have hz : stratA r₁ (c, (a, b, m)) = 0 := by rw [stratA_apply, hcol, hzero]; rfl
      exact hA hz
    have hyB : cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      intro hzero
      have hz : stratB r₁ (c, (a, b, m)) = 0 := by rw [stratB_apply, hcol, hzero]; rfl
      exact hB hz
    have hyM : cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      intro hzero
      have hz : stratM r₁ (c, (a, b, m)) = 0 := by rw [stratM_apply, hcol, hzero]; rfl
      exact hM hz
    have hya : cross3 (velocity (pertV r₁ c) a) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      rwa [← velocity_pertV h₁.smooth c a] at hyA
    have hyb : cross3 (velocity (pertV r₁ c) b) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      rwa [← velocity_pertV h₁.smooth c b] at hyB
    have hym : cross3 (velocity (pertV r₁ c) m) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      rwa [← velocity_pertV h₁.smooth c m] at hyM
    -- the tangent–chord vectors are not all parallel
    have hnoPar : ¬ ∃ la mu : ℝ,
        cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b) =
          la • cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b) ∧
        cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b) =
          mu • cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b) := by
      rintro ⟨la, mu, hla, hmu⟩
      obtain ⟨j, hj⟩ := exists_nat_ge (max |la| |mu|)
      have hmem : mkCfg la mu a b m ∈ Kn k j :=
        mem_Kn_mkCfg (le_trans (le_max_left _ _) hj) (le_trans (le_max_right _ _) hj)
          haI hbI hmI hk1 hk2 hk3
      have hzero : stratPsi r₁ (c, mkCfg la mu a b m) = 0 := by
        rw [stratPsi_apply, cfgA_mkCfg, cfgB_mkCfg, cfgM_mkCfg, cfgLam_mkCfg, cfgMu_mkCfg,
          hcol, hla, hmu]
        simp
      exact hgoodPsi k j _ hmem hzero
    have hmb : pertV r₁ c m - pertV r₁ c b ≠ 0 := hdist.2.2
    refine ⟨?_, ?_⟩
    · -- rank two
      have hcp0 : collParam a b m (0 : Fin 3) = a := rfl
      have hcp1 : collParam a b m (1 : Fin 3) = b := rfl
      have hcp2 : collParam a b m (2 : Fin 3) = m := rfl
      have hpar : (¬ ∃ la : ℝ, cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b) =
          la • cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b)) ∨
          (¬ ∃ mu : ℝ, cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b) =
          mu • cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b)) := by
        by_contra hcon
        push_neg at hcon
        exact hnoPar ⟨hcon.1.choose, hcon.2.choose, hcon.1.choose_spec, hcon.2.choose_spec⟩
      rcases hpar with hpar | hpar
      · have hc : cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
          intro hzero
          exact hpar ⟨0, by rw [hzero, zero_smul]⟩
        refine (rank_two_criterion_at_collinearity_zero (r := pertV r₁ c) (a := a) (b := b)
          (m := m) hdist.1 hdist.2.1 hmb hcol).mpr ⟨0, 1, by norm_num, ?_⟩
        rw [hcp0, hcp1, velocity_pertV h₁.smooth c a, velocity_pertV h₁.smooth c b]
        refine (linearIndependent_pair_iff_cross3_ne_zero _ _).mpr ?_
        intro hzero
        have hzero' : cross3 (cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b))
            (cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b)) = 0 := by
          rw [cross3_anticomm, hzero, neg_zero]
        rcases (cross3_eq_zero_iff_smul_local
          (u := cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b))
          (v := cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b))).mp hzero' with h | h
        · exact hyB h
        · exact hpar ⟨h.choose, h.choose_spec⟩
      · have hc : cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
          intro hzero
          exact hpar ⟨0, by rw [hzero, zero_smul]⟩
        refine (rank_two_criterion_at_collinearity_zero (r := pertV r₁ c) (a := a) (b := b)
          (m := m) hdist.1 hdist.2.1 hmb hcol).mpr ⟨1, 2, by decide, ?_⟩
        rw [hcp1, hcp2, velocity_pertV h₁.smooth c b, velocity_pertV h₁.smooth c m]
        refine (linearIndependent_pair_iff_cross3_ne_zero _ _).mpr ?_
        intro hzero
        rcases (cross3_eq_zero_iff_smul_local
          (u := cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b))
          (v := cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b))).mp hzero with h | h
        · exact hyB h
        · exact hpar ⟨h.choose, h.choose_spec⟩
    · -- endpoint tangents off the chord
      obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ,
          pertV r₁ c a - pertV r₁ c m = ρ • (pertV r₁ c a - pertV r₁ c b) := by
        have hcol' : cross3 (pertV r₁ c a - pertV r₁ c b) (pertV r₁ c a - pertV r₁ c m) = 0 := by
          rwa [collinearityValue_eq] at hcol
        rcases (cross3_eq_zero_iff_smul_local (u := pertV r₁ c a - pertV r₁ c b)
          (v := pertV r₁ c a - pertV r₁ c m)).mp hcol' with h | h
        · exact absurd h hdist.1
        · exact h
      have hρ0 : ρ ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hρ
        exact hdist.2.1 hρ
      have hρ1 : ρ ≠ 1 := by
        intro h1
        have h2 : pertV r₁ c a - pertV r₁ c m = pertV r₁ c a - pertV r₁ c b := by
          rw [hρ, h1, one_smul]
        have h5 := congrArg (fun x : Space => pertV r₁ c a - x) h2
        rw [sub_sub_cancel, sub_sub_cancel] at h5
        exact hdist.2.2 (by rw [h5, sub_self])
      have hρm : pertV r₁ c b - pertV r₁ c m = (ρ - 1) • (pertV r₁ c a - pertV r₁ c b) := by
        have h1 : pertV r₁ c b - pertV r₁ c m
            = -(pertV r₁ c a - pertV r₁ c b) + (pertV r₁ c a - pertV r₁ c m) := by abel
        rw [h1, hρ, sub_smul, one_smul]
        abel
      have hρm0 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
      have hya' : cross3 (velocity (pertV r₁ c) a) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := hya
      have hyb' : cross3 (velocity (pertV r₁ c) b) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := hyb
      have hym' : cross3 (velocity (pertV r₁ c) m) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := hym
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [cross3_anticomm]; exact neg_ne_zero.mpr hya'
      · rw [cross3_anticomm]; exact neg_ne_zero.mpr hyb'
      · rw [hρ, cross3_smul_left]
        exact smul_ne_zero hρ0 (by rw [cross3_anticomm]; exact neg_ne_zero.mpr hya')
      · rw [hρ, cross3_smul_left]
        exact smul_ne_zero hρ0 (by rw [cross3_anticomm]; exact neg_ne_zero.mpr hym')
      · rw [hρm, cross3_smul_left]
        exact smul_ne_zero hρm0 (by rw [cross3_anticomm]; exact neg_ne_zero.mpr hyb')
      · rw [hρm, cross3_smul_left]
        exact smul_ne_zero hρm0 (by rw [cross3_anticomm]; exact neg_ne_zero.mpr hym')
  · -- the curvature is preserved
    intro t
    have hcn : ‖c‖ ≤ r₀ := by
      have hc' := hcKv
      rw [Kv, Metric.mem_closedBall, dist_zero_right] at hc'
      exact hc'
    have hρc : c ∈ Kv ρ := by
      rw [Kv, Metric.mem_closedBall, dist_zero_right]
      linarith
    have h := hρ c hρc t
    have hvel : (fun s : ℝ => pertVelV r₁ c s) = velocity (pertV r₁ c) :=
      funext fun s => (velocity_pertV h₁.smooth c s).symm
    have h' : cross3 (velocity (pertV r₁ c) t) (deriv (velocity (pertV r₁ c)) t) ≠ 0 := by
      rw [← hvel]
      exact h
    exact (linearIndependent_pair_iff_cross3_ne_zero _ _).mpr h'
  · -- no five collinear points
    exact noFiveCollinear_of_not_bad5 hcKv hgood5
  · -- closeness
    intro t
    have hb1 : ‖eCoeff c‖ ≤ Kc * r₀ := hbound c hcKv
    have hb2 : Kc * r₀ ≤ ε/100 := by
      have := mul_le_mul_of_nonneg_left hr₀leε hKcpos.le
      rwa [show Kc * (ε/(100*Kc)) = ε/100 from by field_simp] at this
    constructor
    · have hdiff : pertV r₁ c t - r t = perturbCorr (eCoeff c) t + (r₁ t - r t) := by
        simp [pertV, perturb]
        abel
      rw [hdiff]
      have h2 : ‖perturbCorr (eCoeff c) t‖ ≤ 9 * ‖eCoeff c‖ := norm_perturbCorr_le _ _
      have h5 : ‖r₁ t - r t‖ < ε/2 := (hclose₁ t).1
      calc ‖perturbCorr (eCoeff c) t + (r₁ t - r t)‖
          ≤ ‖perturbCorr (eCoeff c) t‖ + ‖r₁ t - r t‖ := norm_add_le _ _
        _ < ε := by linarith
    · have hdiff : velocity (pertV r₁ c) t - velocity r t
          = perturbVelCorr (eCoeff c) t + (velocity r₁ t - velocity r t) := by
        rw [velocity_pertV h₁.smooth c t]
        simp [pertVelV, perturbVel]
        abel
      rw [hdiff]
      have h2 : ‖perturbVelCorr (eCoeff c) t‖ ≤ 36 * ‖eCoeff c‖ := norm_perturbVelCorr_le _ _
      have h5 : ‖velocity r₁ t - velocity r t‖ < ε/2 := (hclose₁ t).2
      calc ‖perturbVelCorr (eCoeff c) t + (velocity r₁ t - velocity r t)‖
          ≤ ‖perturbVelCorr (eCoeff c) t‖ + ‖velocity r₁ t - velocity r t‖ := norm_add_le _ _
        _ < ε := by linarith

theorem genericNoInflNoFiveDense_of_bad5
    (h5 : ∀ (r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space),
      LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r → ∀ r₀ : ℝ, 0 < r₀ →
      (∀ c ∈ Work.Drive.Kv r₀,
        LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot (Work.Drive.pertV r c)) →
      ∀ k : ℕ, interior (Work.Drive.bad5 r r₀ k) = ∅) :
    Work.Drive.GenericNoInflNoFiveDense := by
  intro r hr ε hε
  exact exists_close_generic_noFive_of_bad5 h5 hr ε hε

end

end Work.Drive
