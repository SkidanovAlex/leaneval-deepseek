import Mathlib
import Submission.Work.NN.Final.PolarChainDefs
import Submission.Work.NN.Final.holderNorm_comp_flatPoint

noncomputable section

set_option maxHeartbeats 1000000

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.PolarChain

/-! ## Agreement of the globally smooth model with the fibre map

The fibre map `flatPoint n ρ j` of the polar construction replaces the `j`-th coordinate of
`p.1` by the point of modulus `ρ j * exp (-p.2)` on the ray of `p.1 j`.  Its only non-smooth
feature is the direction `p.1 j / ‖p.1 j‖`, which is singular at `p.1 j = 0`; the globally
smooth model `flatGlob n ρ j ε` clamps this direction by `ChartComp.u0 (fun _ => 3 * ε) j`,
which equals the direction as soon as `ε ≤ ‖p.1 j‖`.  Hence on the region where the `j`-th
coordinate is bounded below by `ε` the two maps coincide. -/

lemma flatGlob_eq_flatPoint_of_le {n : ℕ} {ρ : Fin n → ℝ} {j : Fin n} {ε : ℝ} (hε : 0 < ε)
    {p : (Fin n → ℂ) × ℝ} (hp : ε ≤ ‖p.1 j‖) :
    Work.NN.Final.flatGlob n ρ j ε p = Work.NN.Final.flatPoint n ρ j p := by
  rw [Work.NN.Final.flatGlob, Work.NN.Final.flatPoint]
  congr 1
  have hstep : Work.NN.Final.radialStep ((3 * ε) / 8) ((3 * ε) / 3) ‖p.1 j‖ = 1 := by
    refine Work.NN.Final.radialStep_of_ge (by linarith) ?_
    linarith
  rw [Work.NN.Final.ChartComp.u0, hstep, Complex.ofReal_one, one_mul,
    Work.NN.Final.ChartComp.dirn, Complex.ofReal_div]
  ring

/-- The flat region of the `j`-th polar step lies inside the auxiliary convex region `flatS`
on which the global model has bounded derivatives. -/
lemma cvFlat_subset_flatS {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) (j : Fin n) :
    Work.NN.Final.cvFlat n ρ j ×ˢ {t : ℝ | 0 < t} ⊆ Work.NN.Final.flatS n ρ := by
  intro p hp
  obtain ⟨hpw, hpt⟩ := Set.mem_prod.mp hp
  rw [Work.NN.Final.mem_cvFlat] at hpw
  obtain ⟨h1, ⟨hj1, hj2⟩, h3⟩ := hpw
  refine Set.mem_prod.mpr ⟨?_, hpt⟩
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]
  have hsum : 0 ≤ ∑ i, ρ i := Finset.sum_nonneg fun i _ => le_of_lt (hρ i)
  have hb : ‖p.1‖ ≤ 3 * ∑ i, ρ i :=
    (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) hsum)).mpr fun i => by
      have hc := Work.NN.Final.chainC_lt_three n (j : ℕ) (le_of_lt j.isLt)
      have hd := Work.NN.Final.chainD_lt_three n (j : ℕ) (le_of_lt j.isLt)
      have hp' := hρ i
      have hle : ρ i ≤ ∑ k, ρ k :=
        Finset.single_le_sum (fun k _ => le_of_lt (hρ k)) (Finset.mem_univ i)
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
      · have hi := h1 i h
        nlinarith
      · have hji : i = j := Fin.ext h
        subst hji
        nlinarith
      · have hi := h3 i h
        nlinarith
  rw [Work.NN.Final.flatRad]
  linarith

/-- The fibre map of the flat picture is `C^{k,α}` uniformly on the flat region `cvFlat` of the
`j`-th polar step, with the input `G` measured on the level-`(j+1)` chain region: for every order
`k` there is a constant `C k > 0` with
`‖flatPull n ρ j G‖_{C^{k,α}(cvFlat j × (0,∞))} ≤ C k * ‖G‖_{C^{k,α}(cvReg (j+1))}`. -/
theorem flatPoint_comp_cvFlat {n : ℕ} {ρ : Fin n → ℝ} (hρ : ∀ i, 0 < ρ i) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (j : Fin n) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧ ∀ (k : ℕ) (G : (Fin n → ℂ) → ℂ),
      ContDiffOn ℝ (k : WithTop ENat) G (Work.NN.Final.cvReg n ρ ((j : ℕ) + 1)) →
      Work.CR.Flat.holderNorm k α (Work.NN.Final.flatPull n ρ j G) (Set.prod (Work.NN.Final.cvFlat n ρ j) {t : ℝ | 0 < t})
        ≤ ENNReal.ofReal (C k) *
          Work.CR.Flat.holderNorm k α G (Work.NN.Final.cvReg n ρ ((j : ℕ) + 1)) := by
  classical
  have hεpos : (0 : ℝ) < ρ j / 4 := by have := hρ j; linarith
  obtain ⟨D, hD0, hDb⟩ :=
    Work.NN.Final.exists_bound_flatGlob (n := n) ρ j (ε := ρ j / 4) hεpos
  obtain ⟨L, _hL0, hL⟩ :=
    Work.NN.Final.exists_lipschitz_flatGlob (n := n) ρ j (ε := ρ j / 4) hεpos
  obtain ⟨E, hE⟩ :=
    Work.NN.Final.exists_holderE_flatGlob (n := n) ρ j (ε := ρ j / 4) hεpos hα0 hα1
  set s : Set ((Fin n → ℂ) × ℝ) := Set.prod (Work.NN.Final.cvFlat n ρ j) {t : ℝ | 0 < t} with hs
  have hsopen : IsOpen s := (Work.NN.Final.isOpen_cvFlat hρ j).prod isOpen_Ioi
  have htopen : IsOpen (Work.NN.Final.cvReg n ρ ((j : ℕ) + 1)) :=
    Work.NN.Final.isOpen_cvReg hρ ((j : ℕ) + 1)
  have hsub : s ⊆ Work.NN.Final.flatS n ρ := by
    rw [hs]; exact cvFlat_subset_flatS hρ j
  -- the model agrees with the fibre map on `s`
  have hglob_eq : ∀ p ∈ s,
      Work.NN.Final.flatPoint n ρ j p = Work.NN.Final.flatGlob n ρ j (ρ j / 4) p := by
    intro p hp
    rw [hs] at hp
    obtain ⟨hpw, hp2⟩ := Set.mem_prod.mp hp
    rw [Work.NN.Final.mem_cvFlat] at hpw
    have hle : ρ j / 4 ≤ ‖p.1 j‖ := by have := hpw.2.1; linarith
    exact (flatGlob_eq_flatPoint_of_le (n := n) (ρ := ρ) (j := j) hεpos hle).symm
  have hst : Set.MapsTo (Work.NN.Final.flatPoint n ρ j) s
      (Work.NN.Final.cvReg n ρ ((j : ℕ) + 1)) := by
    intro p hp
    rw [hs] at hp
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    have hmem : p ∈ (Work.NN.Final.cvFlat n ρ j ×ˢ {t : ℝ | 0 ≤ t}) := by
      rw [Set.mem_prod, Set.mem_ofPred_eq]
      exact ⟨hp1, le_of_lt hp2⟩
    exact Work.NN.Final.flatPoint_mapsTo_cvReg hρ j hmem
  have hΦ : ∀ m : ℕ, ContDiffOn ℝ (m : WithTop ENat) (Work.NN.Final.flatPoint n ρ j) s := by
    intro m
    have h1 : ContDiffOn ℝ (m : WithTop ENat)
        (Work.NN.Final.flatGlob n ρ j (ρ j / 4)) s :=
      (Work.NN.Final.contDiff_flatGlob (n := n) (ρ := ρ) (j := j) hεpos).contDiffOn.of_le
        (Work.NN.Final.ChartComp.natCast_le_top_nat m)
    exact h1.congr (fun p hp => hglob_eq p hp)
  have hL' : ∀ x ∈ s, ∀ y ∈ s,
      ‖Work.NN.Final.flatPoint n ρ j x - Work.NN.Final.flatPoint n ρ j y‖ ≤ L * ‖x - y‖ := by
    intro x hx y hy
    rw [hglob_eq x hx, hglob_eq y hy]
    exact hL x (hsub hx) y (hsub hy)
  -- transfer of the derivative bounds from the model to the fibre map
  have hkey : ∀ (k : ℕ) (x : (Fin n → ℂ) × ℝ), x ∈ s →
      iteratedFDerivWithin ℝ k (Work.NN.Final.flatPoint n ρ j) s x
        = iteratedFDerivWithin ℝ k (Work.NN.Final.flatGlob n ρ j (ρ j / 4))
            (Work.NN.Final.flatS n ρ) x := by
    intro k x hx
    have h1 : iteratedFDerivWithin ℝ k (Work.NN.Final.flatPoint n ρ j) s x
        = iteratedFDerivWithin ℝ k (Work.NN.Final.flatGlob n ρ j (ρ j / 4)) s x :=
      iteratedFDerivWithin_congr (fun z hz => hglob_eq z hz) hx k
    have h2 : iteratedFDerivWithin ℝ k (Work.NN.Final.flatGlob n ρ j (ρ j / 4)) s x
        = iteratedFDerivWithin ℝ k (Work.NN.Final.flatGlob n ρ j (ρ j / 4))
            (Work.NN.Final.flatS n ρ) x := by
      rw [iteratedFDerivWithin_of_isOpen k hsopen hx,
        iteratedFDerivWithin_of_isOpen k (Work.NN.Final.isOpen_flatS n ρ) (hsub hx)]
    rw [h1, h2]
  have hD' : ∀ (k : ℕ) (x : (Fin n → ℂ) × ℝ), x ∈ s →
      ‖iteratedFDerivWithin ℝ k (Work.NN.Final.flatPoint n ρ j) s x‖ ≤ D k := by
    intro k x hx
    rw [hkey k x hx]
    exact hDb k x (hsub hx)
  have hE' : ∀ (k : ℕ) (x : (Fin n → ℂ) × ℝ), x ∈ s → ∀ y ∈ s,
      ‖iteratedFDerivWithin ℝ k (Work.NN.Final.flatPoint n ρ j) s x
        - iteratedFDerivWithin ℝ k (Work.NN.Final.flatPoint n ρ j) s y‖
        ≤ E k * ‖x - y‖ ^ α := by
    intro k x hx y hy
    rw [hkey k x hx, hkey k y hy,
      iteratedFDerivWithin_of_isOpen k (Work.NN.Final.isOpen_flatS n ρ) (hsub hx),
      iteratedFDerivWithin_of_isOpen k (Work.NN.Final.isOpen_flatS n ρ) (hsub hy)]
    exact hE k x (hsub hx) y (hsub hy)
  obtain ⟨C, hC0, hC⟩ := Work.CR.Flat.Holder.holderNorm_comp_le_of_contDiffOn
    (Φ := Work.NN.Final.flatPoint n ρ j) (s := s)
    (t := Work.NN.Final.cvReg n ρ ((j : ℕ) + 1))
    hst hΦ hsopen htopen L hL' α hα0 D hD' E hE'
  refine ⟨C, hC0, fun k G hG => ?_⟩
  have h := hC k G hG
  have hfun : Work.NN.Final.flatPull n ρ j G = G ∘ Work.NN.Final.flatPoint n ρ j := rfl
  rw [hfun]
  exact h

end Work.NN.PolarChain
