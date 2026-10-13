/-
  WilG1 / Thin / oneDim_fin

  Finiteness of the sets appearing in the cover of the non-differentiability set:
  `oscR g q`, `oscL g q` (which are `Ω`-definable and have empty interior) and
  `infDeriv g 1`, `infDeriv g (-1)` (likewise).
-/
import Mathlib
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.OneDim.oscillation_empty
import Submission.Work.WilG1.Thin.infderiv_mem
import Submission.Work.WilG1.Thin.oneDim_oscL_empty
import Submission.Work.WilG1.Thin.oneDim_pred
import Submission.Work.WilG1.Calc.finite_of_interior_empty

set_option autoImplicit false
noncomputable section

open Classical Filter Topology
open scoped Topology

namespace Work.WilG1.Thin

open WilkiesDesign WilkiesConjecture Work.WilG1 WilkiesDesign.CG

/-! ## 0. Between `ℝ` and `Fin 1 → ℝ` -/

/-- The canonical homeomorphism `(Fin 1 → ℝ) ≃ₜ ℝ`. -/
def e1 : (Fin 1 → ℝ) ≃ₜ ℝ := Homeomorph.funUnique (Fin 1) ℝ

lemma e1_apply (z : Fin 1 → ℝ) : e1 z = z 0 := by
  rw [show e1 = Homeomorph.funUnique (Fin 1) ℝ from rfl, Homeomorph.funUnique_apply]
  exact congrArg z (Subsingleton.elim default 0)

lemma liftR_eq_preimage (A : Set ℝ) : liftR A = e1 ⁻¹' A := by
  ext z
  rw [liftR, Set.mem_ofPred_eq, Set.mem_preimage, e1_apply]

lemma interior_liftR_empty_iff (A : Set ℝ) : interior (liftR A) = ∅ ↔ interior A = ∅ := by
  rw [liftR_eq_preimage, ← Homeomorph.preimage_interior]
  constructor
  · intro h
    have himg : e1 '' (e1 ⁻¹' interior A) = interior A :=
      Set.image_preimage_eq _ e1.surjective
    rw [← himg, h, Set.image_empty]
  · intro h
    rw [h, Set.preimage_empty]

lemma finite_liftR_iff (A : Set ℝ) : (liftR A).Finite ↔ A.Finite := by
  constructor
  · intro h
    have himg : e1 '' (liftR A) = A := by
      rw [liftR_eq_preimage, Set.image_preimage_eq _ e1.surjective]
    rw [← himg]
    exact h.image _
  · intro h
    rw [liftR_eq_preimage]
    exact h.preimage (fun _ _ _ _ hxy => e1.injective hxy)

/-- An interval is not countable. -/
theorem not_countable_Ioo {a b : ℝ} (h : a < b) : ¬ (Set.Ioo a b).Countable := by
  intro hc
  have h1 : Cardinal.mk (Set.Ioo a b) ≤ Cardinal.aleph0 :=
    Cardinal.mk_le_aleph0_iff.mpr hc.to_subtype
  rw [Cardinal.mk_Ioo_real h] at h1
  exact absurd h1 (not_le.mpr Cardinal.aleph0_lt_continuum)

/-! ## 1. The two oscillation sets -/

theorem finite_oscR {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (q : ℝ) :
    (oscR g q).Finite := by
  obtain ⟨a, b, hmem⟩ := oscR_mem (S := S) (F := F) (D := D) g hg q
  have hint : interior (oscR g q) = ∅ := by
    have h := Work.WilG1.OneDim.oscillation_empty (S := S) (F := F) (D := D) q g hg
    simpa only [oscR, dq] using h
  exact (finite_liftR_iff (oscR g q)).mp
    (Work.WilG1.Calc.finite_of_interior_empty hmem ((interior_liftR_empty_iff (oscR g q)).mpr hint))

theorem finite_oscL {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (q : ℝ) :
    (oscL g q).Finite := by
  obtain ⟨a, b, hmem⟩ := oscL_mem (S := S) (F := F) (D := D) g hg q
  have hint : interior (oscL g q) = ∅ := oneDim_oscL_empty (S := S) (F := F) (D := D) g hg q
  exact (finite_liftR_iff (oscL g q)).mp
    (Work.WilG1.Calc.finite_of_interior_empty hmem ((interior_liftR_empty_iff (oscL g q)).mpr hint))

/-! ## 2. The infinite-derivative sets -/

/-- On a set on which the two-sided difference quotient tends to `+∞` at every point no two
points are comparable: the estimate propagates from `a` to `b` along the interval. -/
theorem subsingleton_of_dq_tendsto_atTop {f : ℝ → ℝ} {I : Set ℝ} (hI : I.OrdConnected)
    (hlim : ∀ x ∈ I, ∀ M : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℝ, y ≠ x → |y - x| < δ →
      M < (f y - f x) / (y - x)) : I.Subsingleton := by
  have main : ∀ {a b : ℝ}, a ∈ I → b ∈ I → a < b → False := by
    intro a b ha hb hab
    have hIcc : Set.Icc a b ⊆ I := hI.out ha hb
    have hprop : ∀ M : ℝ, f a + M * (b - a) ≤ f b := by
      intro M
      by_contra hcon
      push_neg at hcon
      set T : Set ℝ := {w | w ∈ Set.Icc a b ∧ f w < f a + M * (w - a)} with hT
      have hbT : b ∈ T := ⟨⟨hab.le, le_rfl⟩, hcon⟩
      have hbdd : BddBelow T := ⟨a, fun w hw => hw.1.1⟩
      have hne : T.Nonempty := ⟨b, hbT⟩
      set t : ℝ := sInf T with ht
      have htIcc : t ∈ Set.Icc a b := by
        refine ⟨?_, ?_⟩
        · rw [ht]; exact le_csInf hne (fun w hw => hw.1.1)
        · rw [ht]; exact csInf_le hbdd hbT
      have htI : t ∈ I := hIcc htIcc
      -- the estimate at `t` forces `t ∉ T`
      have htnt : t ∉ T := by
        intro htT
        have hft : f t < f a + M * (t - a) := htT.2
        have hta : a < t := by
          rcases eq_or_lt_of_le htIcc.1 with h | h
          · exfalso; rw [h] at hft; linarith
          · exact h
        obtain ⟨δ, hδ, hδ'⟩ := hlim t htI M
        set u : ℝ := max a (t - δ / 2) with hu
        set y : ℝ := (u + t) / 2 with hy
        have hut : u < t := max_lt hta (by linarith)
        have huy : u < y := by rw [hy]; linarith
        have hyt : y < t := by rw [hy]; linarith
        have hay : a ≤ y := le_trans (le_max_left _ _) huy.le
        have hyT : y ∈ T := by
          refine ⟨⟨hay, le_trans hyt.le htIcc.2⟩, ?_⟩
          have hne' : y ≠ t := ne_of_lt hyt
          have habs : |y - t| < δ := by
            have h3 : t - u ≤ δ / 2 := by
              have := le_max_right a (t - δ / 2)
              rw [hu]; linarith
            rw [abs_of_neg (by linarith)]
            linarith
          have hlim' := hδ' y hne' habs
          have hlt : f y - f t < M * (y - t) := (lt_div_iff_of_neg (by linarith)).mp hlim'
          linarith
        have := csInf_le hbdd hyT
        rw [← ht] at this
        linarith
      have hft2 : f a + M * (t - a) ≤ f t := by
        by_contra hcon'
        push_neg at hcon'
        exact htnt ⟨htIcc, hcon'⟩
      obtain ⟨δ, hδ, hδ'⟩ := hlim t htI M
      have hright : ∀ y : ℝ, t < y → y < t + δ → y ∉ T := by
        intro y hty hyt hyT
        have hne' : y ≠ t := ne_of_gt hty
        have habs : |y - t| < δ := by
          rw [abs_of_pos (by linarith)]
          linarith
        have hlim' := hδ' y hne' habs
        have hlt : M * (y - t) < f y - f t := (lt_div_iff₀ (by linarith)).mp hlim'
        have hyT' : f y < f a + M * (y - a) := hyT.2
        nlinarith [hlt, hyT', hft2, hty]
      rcases lt_or_eq_of_le htIcc.2 with hltb | heqb
      · -- `t < b`: then `T` stays above `t + min (b - t) δ > t`
        have hμ : 0 < min (b - t) δ := lt_min (by linarith) hδ
        have hlow : ∀ w ∈ T, t + min (b - t) δ ≤ w := by
          intro w hw
          have hwt : t ≤ w := by
            have := csInf_le hbdd hw
            rw [← ht] at this
            exact this
          rcases lt_or_eq_of_le hwt with h | h
          · by_contra hcon''
            push_neg at hcon''
            have hδw : w < t + δ := by
              have : min (b - t) δ ≤ δ := min_le_right _ _
              linarith
            exact hright w h hδw hw
          · rw [← h] at hw
            exact absurd hw htnt
        have := le_csInf hne hlow
        rw [← ht] at this
        linarith
      · -- `t = b`: then `T = {b}`, contradicted by a point just below `b`
        have hTeq : T = {b} := by
          ext w
          constructor
          · intro hw
            have hwt : t ≤ w := by
              have := csInf_le hbdd hw
              rw [← ht] at this
              exact this
            have hwb : w ≤ b := hw.1.2
            rw [heqb] at hwt
            exact le_antisymm hwb hwt
          · intro hw
            rw [Set.mem_singleton_iff] at hw
            rw [hw]; exact hbT
        set u : ℝ := max a (b - δ / 2) with hu
        set y : ℝ := (u + b) / 2 with hy
        have hub : u < b := max_lt hab (by linarith)
        have huy : u < y := by rw [hy]; linarith
        have hyb : y < b := by rw [hy]; linarith
        have hay : a ≤ y := le_trans (le_max_left _ _) huy.le
        have hyT : y ∉ T := by
          rw [hTeq]
          intro hmem
          exact absurd (Set.mem_singleton_iff.mp hmem) (ne_of_lt hyb)
        have hyge : f a + M * (y - a) ≤ f y := by
          by_contra hcon''
          push_neg at hcon''
          exact hyT ⟨⟨hay, hyb.le⟩, hcon''⟩
        have hδy : b - y < δ := by
          have h3 : b - u ≤ δ / 2 := by
            have := le_max_right a (b - δ / 2)
            rw [hu]; linarith
          linarith
        have hyt : y ≠ t := by rw [heqb]; exact ne_of_lt hyb
        have hyt' : y < t := by rw [heqb]; exact hyb
        have habs : |y - t| < δ := by
          rw [abs_of_neg (by rw [heqb]; linarith)]
          rw [heqb]
          linarith
        have hlim' := hδ' y hyt habs
        have hlt : f y - f t < M * (y - t) :=
          (lt_div_iff_of_neg (by rw [heqb]; linarith)).mp hlim'
        rw [← heqb] at hcon
        nlinarith [hlt, hyge, hcon, hyt']
    have hpos : 0 < b - a := by linarith
    have hM := hprop ((f b - f a) / (b - a) + 1)
    have hMc : (f b - f a) / (b - a) * (b - a) = f b - f a :=
      div_mul_cancel₀ _ (ne_of_gt hpos)
    nlinarith [hM, hpos, hMc]
  intro a ha b hb
  rcases lt_trichotomy a b with hab | heq | hba
  · exact (main ha hb hab).elim
  · exact heq
  · exact (main hb ha hba).elim

/-- The difference quotient of the negation. -/
theorem dq_neg (g : ℝ → ℝ) (y z : ℝ) : dq (fun t => -g t) y z = -dq g y z := by
  simp only [dq, Pi.neg_apply, neg_div]
  ring

theorem interior_infDeriv_one_empty (g : ℝ → ℝ) : interior (infDeriv g 1) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hnb : (infDeriv g 1 : Set ℝ) ∈ 𝓝 x := by
    rwa [mem_interior_iff_mem_nhds] at hx
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnb
  have hI : Set.Ioo (x - ε) (x + ε) ⊆ infDeriv g 1 := by
    intro y hy
    refine hsub ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hsingle := subsingleton_of_dq_tendsto_atTop (f := g)
    (isPreconnected_iff_ordConnected.mp isPreconnected_Ioo) (fun y hy M => by
      have hyinf : y ∈ infDeriv g 1 := hI hy
      obtain ⟨M', hM1, hM2⟩ : ∃ M' : ℝ, 1 < M' ∧ M ≤ M' :=
        ⟨max M 2, by linarith [le_max_right M 2], le_max_left M 2⟩
      obtain ⟨δ, hδ, hδ'⟩ := hyinf M' hM1
      refine ⟨δ, hδ, fun z hz hzδ => ?_⟩
      have hlt : M' < dq g y z := by simpa using hδ' z hz hzδ
      exact lt_of_le_of_lt hM2 hlt)
  have h1 : x - ε / 2 ∈ Set.Ioo (x - ε) (x + ε) := ⟨by linarith, by linarith⟩
  have h2 : x + ε / 2 ∈ Set.Ioo (x - ε) (x + ε) := ⟨by linarith, by linarith⟩
  exact absurd (hsingle h1 h2) (by linarith)

theorem interior_infDeriv_neg_one_empty (g : ℝ → ℝ) : interior (infDeriv g (-1)) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  have hnb : (infDeriv g (-1) : Set ℝ) ∈ 𝓝 x := by
    rwa [mem_interior_iff_mem_nhds] at hx
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnb
  have hI : Set.Ioo (x - ε) (x + ε) ⊆ infDeriv g (-1) := by
    intro y hy
    refine hsub ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hsingle := subsingleton_of_dq_tendsto_atTop (f := fun t => -g t)
    (isPreconnected_iff_ordConnected.mp isPreconnected_Ioo) (fun y hy M => by
      have hyinf : y ∈ infDeriv g (-1) := hI hy
      obtain ⟨M', hM1, hM2⟩ : ∃ M' : ℝ, 1 < M' ∧ M ≤ M' :=
        ⟨max M 2, by linarith [le_max_right M 2], le_max_left M 2⟩
      obtain ⟨δ, hδ, hδ'⟩ := hyinf M' hM1
      refine ⟨δ, hδ, fun z hz hzδ => ?_⟩
      have hlt : M' < (-1 : ℝ) * dq g y z := hδ' z hz hzδ
      have h2 : M < -dq g y z := by linarith
      have h3 : dq (fun t => -g t) y z = -dq g y z := dq_neg g y z
      show M < dq (fun t => -g t) y z
      rw [h3]
      exact h2)
  have h1 : x - ε / 2 ∈ Set.Ioo (x - ε) (x + ε) := ⟨by linarith, by linarith⟩
  have h2 : x + ε / 2 ∈ Set.Ioo (x - ε) (x + ε) := ⟨by linarith, by linarith⟩
  exact absurd (hsingle h1 h2) (by linarith)

theorem finite_infDeriv_one {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) : (infDeriv g 1).Finite := by
  have hmem : liftR (infDeriv g 1) ∈ S.Ω (F + 1000)
      ((Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1)).eval D) 1 :=
    infderiv_mem (S := S) (F := F) (D := D) g hg 1
  exact (finite_liftR_iff (infDeriv g 1)).mp
    (Work.WilG1.Calc.finite_of_interior_empty hmem
      ((interior_liftR_empty_iff (infDeriv g 1)).mpr (interior_infDeriv_one_empty g)))

theorem finite_infDeriv_neg_one {S : WilkiesDesign.SOMin} {F D : ℕ} (g : ℝ → ℝ)
    (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) : (infDeriv g (-1)).Finite := by
  have hmem : liftR (infDeriv g (-1)) ∈ S.Ω (F + 1000)
      ((Polynomial.C 1000 * (Polynomial.X + Polynomial.C 1)).eval D) 1 :=
    infderiv_mem (S := S) (F := F) (D := D) g hg (-1)
  exact (finite_liftR_iff (infDeriv g (-1))).mp
    (Work.WilG1.Calc.finite_of_interior_empty hmem
      ((interior_liftR_empty_iff (infDeriv g (-1))).mpr (interior_infDeriv_neg_one_empty g)))

end Work.WilG1.Thin
