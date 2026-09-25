import Mathlib
import Submission.Work.NN.Final.flatTwoSupportRegion

namespace Work.NN.Final

noncomputable section
open scoped NNReal ENNReal ContDiff
open Set
open Work.CR.Flat

set_option maxHeartbeats 1000000

/-- Membership in the polydisc of centre `0`, in normalised form. -/
lemma tun_mem_polydisc_zero {n : ℕ} {r : Fin n → ℝ} {z : Fin n → ℂ} :
    z ∈ polydisc (0 : Fin n → ℂ) r ↔ ∀ j, ‖z j‖ < r j := by
  simp [polydisc]

/-! ## Parametric (tunable-radius) versions of the auxiliary estimates of
`flatTwoSupportRegion.lean`

`flatTwoSupportRegion` runs one Bochner–Martinelli step plus the transferred loss-free `(0,2)`
recursion on the fixed chain of regions `8/3 < 17/6 < 29/10 < 3`.  Every ingredient of that
construction is parametric in the radii; below we record the parametric versions of the auxiliary
lemmas of `flatTwoSupportRegion.lean` (which hardcode `3, 29/10, 17/6, 8/3`), so that the main
theorem can be re-run with a chain `1 < c₁ < c₂ < c` and the output polydisc `polydisc 0 ρ`. -/

/-! ### Product estimates with the datum only on the polydisc `polydisc 0 R` -/

/-- The `C^{k,α}`-norm on `ℂⁿ` of `χ · f`, where `χ` is compactly supported and smooth with
`tsupport χ ⊆ polydisc 0 r` and `f` is only known on `polydisc 0 R` (`r < R`), is controlled by
the `C^{k,α}`-norm of `f` on `polydisc 0 R`.  Parametric `chiMul_univ_le`. -/
lemma tun_chiMul {n : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {r R : Fin n → ℝ} (hrR : ∀ j, r j < R j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ polydisc 0 r) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ (k : ℕ∞) f (polydisc 0 R) →
      holderNorm k α (fun z => χ z * f z) Set.univ
        ≤ ENNReal.ofReal C * holderNorm k α f (polydisc 0 R) := by
  obtain ⟨C, hC0, hC⟩ := Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
    (Ω := polydisc 0 R) (isOpen_polydisc 0 R).uniqueDiffOn hα0 hα1 (hχ.of_le (by simp)) hcs
  refine ⟨C, hC0, fun f hf => ?_⟩
  refine (Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
    (c := 0) (r := r) (r' := R) (k := k) (g := fun z => χ z * f z) hrR hα0 ?_).trans
    (hC f hf)
  · intro z hz
    obtain ⟨i, hi⟩ := hz
    simp only [Pi.zero_apply, sub_zero] at hi
    have hzn : z ∉ polydisc 0 r := by
      intro h
      have h' : ‖z i‖ < r i := by simpa only [Pi.zero_apply, sub_zero] using h i
      exact absurd h' (not_lt.mpr hi)
    have hts : z ∉ tsupport χ := fun h => hzn (htsupp h)
    show χ z * f z = 0
    rw [Function.notMem_support.mp (fun h => hts (subset_tsupport χ h)), zero_mul]

/-- The `C^{k,α}`-norm on `ℂⁿ` of `∂̄_a χ · f`, where `χ` is compactly supported and smooth with
`tsupport χ ⊆ polydisc 0 r` and `f` is only known on `polydisc 0 R` (`r < R`), is controlled by
the `C^{k,α}`-norm of `f` on `polydisc 0 R` — with a constant uniform in `a`.  Parametric
`dbarCoord_mul_univ_le_pd3`. -/
lemma tun_dbarCoordMul {n : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {r R : Fin n → ℝ} (hrR : ∀ j, r j < R j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ polydisc 0 r) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin n) (f : (Fin n → ℂ) → ℂ),
      ContDiffOn ℝ (k : ℕ∞) f (polydisc 0 R) →
      holderNorm k α (fun w => dbarCoord a χ w * f w) Set.univ
        ≤ ENNReal.ofReal C * holderNorm k α f (polydisc 0 R) := by
  have hper : ∀ a : Fin n, ∃ Ca : ℝ, 0 < Ca ∧ ∀ f : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ (k : ℕ∞) f (polydisc 0 R) →
      holderNorm k α (fun w => dbarCoord a χ w * f w) Set.univ
        ≤ ENNReal.ofReal Ca * holderNorm k α f (polydisc 0 R) := fun a =>
    tun_chiMul (α := α) (r := r) (R := R) (χ := fun w => dbarCoord a χ w) hα0 hα1 hrR
      (Work.NN.Assemble.FT.contDiff_dbarCoord_of hχ a)
      (Work.NN.Assemble.FT.hasCompactSupport_dbarCoord hcs a)
      ((Work.NN.Assemble.FT.tsupport_dbarCoord_subset a).trans htsupp) k
  choose Cd hCdpos hCd using hper
  have hsumpos : 0 < ∑ a : Fin n, Cd a + 1 := by
    have h := Finset.sum_nonneg (fun a (_ : a ∈ Finset.univ) => le_of_lt (hCdpos a))
    linarith
  refine ⟨∑ a, Cd a + 1, hsumpos, fun a f hf => ?_⟩
  refine (hCd a f hf).trans ?_
  refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
  have h1 := Finset.single_le_sum (f := fun a : Fin n => Cd a)
    (fun i _ => le_of_lt (hCdpos i)) (Finset.mem_univ a)
  linarith

/-- Every component of `bmH χ η j l ·` has finite `C^{0,α}`-norm on `ℂⁿ`, bounded uniformly in
`j l i` by the `C^{0,α}`-norm of `η` on `polydisc 0 R`, when `tsupport χ ⊆ polydisc 0 r` with
`r < R`.  Parametric `bmH_univ_le_pd3`. -/
lemma tun_bmH {n : ℕ} {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    {r R : Fin n → ℝ} (hrR : ∀ j, r j < R j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ polydisc 0 r) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ i l, ContDiffOn ℝ (0 : ℕ∞) (η i l) (polydisc 0 R)) → ∀ j l i : Fin n,
        holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ
          ≤ ENNReal.ofReal C * (∑ a : Fin n, ∑ b : Fin n,
              holderNorm 0 α (η a b) (polydisc 0 R)) := by
  have htsuppR : tsupport χ ⊆ polydisc 0 R :=
    htsupp.trans (polydisc_mono fun j => le_of_lt (hrR j))
  obtain ⟨Cd, hCdpos, hCd⟩ :=
    tun_dbarCoordMul (α := α) (r := r) (R := R) hα0 hα1 hrR hχ hcs htsupp 0
  refine ⟨3 * Cd + 1, by linarith, ?_⟩
  intro η hη j l i
  set S : ℝ≥0∞ := ∑ a : Fin n, ∑ b : Fin n, holderNorm 0 α (η a b) (polydisc 0 R) with hSdef
  have hpr : ∀ (a b c : Fin n),
      holderNorm 0 α (fun w => dbarCoord a χ w * η b c w) Set.univ
        ≤ ENNReal.ofReal Cd * S := by
    intro a b c
    refine (hCd a (η b c) (hη b c)).trans (mul_le_mul_right ?_ _)
    rw [hSdef]
    exact le_trans
      (Finset.single_le_sum (f := fun b' : Fin n => holderNorm 0 α (η b b') (polydisc 0 R))
        (fun _ _ => zero_le) (Finset.mem_univ c))
      (Finset.single_le_sum
        (f := fun a' : Fin n => ∑ b' : Fin n, holderNorm 0 α (η a' b') (polydisc 0 R))
        (fun _ _ => zero_le) (Finset.mem_univ b))
  have hsm : ∀ (a b c : Fin n), ContDiff ℝ 0 (fun w => dbarCoord a χ w * η b c w) :=
    fun a b c =>
      Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 0) (isOpen_polydisc 0 R)
        (Work.NN.Assemble.FT.contDiff_dbarCoord_of hχ a)
        ((Work.NN.Assemble.FT.tsupport_dbarCoord_subset a).trans htsuppR) (hη b c)
  have hfun : (fun w => Work.NN.Core.bmH χ η j l i w)
      = (fun w => dbarCoord i χ w * η j l w)
        + ((fun w => dbarCoord j χ w * η l i w)
            + -(fun w => dbarCoord l χ w * η j i w)) := by
    funext w
    rw [Work.NN.Assemble.FT.bmH_eq_sum]
    simp only [Pi.add_apply, Pi.neg_apply]
    ring
  have h1 := Work.CR.Flat.Holder.holderNorm_add_le
    (f := fun w => dbarCoord i χ w * η j l w)
    (g := (fun w => dbarCoord j χ w * η l i w)
      + -(fun w => dbarCoord l χ w * η j i w))
    (Ω := Set.univ) (α := α) (hsm i j l).contDiffOn
    ((hsm j l i).add (hsm l j i).neg).contDiffOn isOpen_univ.uniqueDiffOn
  have h2 := Work.CR.Flat.Holder.holderNorm_add_le
    (f := fun w => dbarCoord j χ w * η l i w)
    (g := -(fun w => dbarCoord l χ w * η j i w))
    (Ω := Set.univ) (α := α) (hsm j l i).contDiffOn ((hsm l j i).neg).contDiffOn
    isOpen_univ.uniqueDiffOn
  have hneg := Work.CR.Flat.Holder.holderNorm_neg
    (f := fun w => dbarCoord l χ w * η j i w) (Ω := Set.univ) (α := α)
    (hsm l j i).contDiffOn isOpen_univ.uniqueDiffOn
  have hthree : ENNReal.ofReal Cd * S + (ENNReal.ofReal Cd * S + ENNReal.ofReal Cd * S)
      = ENNReal.ofReal (3 * Cd) * S := by
    have h3 : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by norm_num
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), h3]
    ring
  calc holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ
      = holderNorm 0 α ((fun w => dbarCoord i χ w * η j l w)
          + ((fun w => dbarCoord j χ w * η l i w)
              + -(fun w => dbarCoord l χ w * η j i w))) Set.univ := by rw [hfun]
    _ ≤ holderNorm 0 α (fun w => dbarCoord i χ w * η j l w) Set.univ
          + holderNorm 0 α ((fun w => dbarCoord j χ w * η l i w)
              + -(fun w => dbarCoord l χ w * η j i w)) Set.univ := h1
    _ ≤ ENNReal.ofReal Cd * S + (ENNReal.ofReal Cd * S + ENNReal.ofReal Cd * S) :=
        add_le_add (hpr i j l)
          (h2.trans (add_le_add (hpr j l i) (by rw [hneg]; exact hpr l j i)))
    _ = ENNReal.ofReal (3 * Cd) * S := hthree
    _ ≤ ENNReal.ofReal (3 * Cd + 1) * S := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        linarith

/-! ### The defect `Edat` of one Bochner–Martinelli step, parametrically -/

/-- Antisymmetry of `bmH χ η` from antisymmetry of `η` only on `polydisc 0 r`.  Parametric
`bmH_antisymm_pd3`. -/
lemma tun_bmH_antisymm {n : ℕ} {r : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (htsupp : tsupport χ ⊆ polydisc 0 r) {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hanti : ∀ i l z, z ∈ polydisc 0 r → η i l z = -η l i z) :
    ∀ j l i w, Work.NN.Core.bmH χ η j l i w = - Work.NN.Core.bmH χ η l j i w := by
  intro j l i w
  rw [Work.NN.Assemble.FT.bmH_eq_sum, Work.NN.Assemble.FT.bmH_eq_sum]
  by_cases hw : w ∈ polydisc 0 r
  · rw [hanti j l w hw, hanti l j w hw]; ring
  · have h0 : ∀ a : Fin n, dbarCoord a χ w = 0 := fun a => by
      by_contra hne
      exact hw (htsupp (Work.NN.Assemble.FT.tsupport_dbarCoord_subset a
        (subset_tsupport _ (Function.mem_support.mpr hne))))
    rw [h0 i, h0 j, h0 l]; ring

/-- The components of `bmH χ η` are globally `C¹` when `tsupport χ ⊆ polydisc 0 r` and `η` is `C¹`
there.  Parametric `contDiff_bmH_pd3`. -/
lemma tun_contDiff_bmH {n : ℕ} {r : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (htsupp : tsupport χ ⊆ polydisc 0 r)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 r)) (j l i : Fin n) :
    ContDiff ℝ 1 (fun w => Work.NN.Core.bmH χ η j l i w) := by
  rw [show (fun w => Work.NN.Core.bmH χ η j l i w)
      = fun w => dbarCoord i χ w * η j l w
          + dbarCoord j χ w * η l i w
          - dbarCoord l χ w * η j i w from by
    funext w; rw [Work.NN.Assemble.FT.bmH_eq_sum]]
  have h1 : ContDiff ℝ 1 (fun w => dbarCoord i χ w * η j l w) :=
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_polydisc 0 r)
      (Work.NN.Assemble.FT.contDiff_dbarCoord_of hχ i)
      ((Work.NN.Assemble.FT.tsupport_dbarCoord_subset i).trans htsupp) (hη j l)
  have h2 : ContDiff ℝ 1 (fun w => dbarCoord j χ w * η l i w) :=
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_polydisc 0 r)
      (Work.NN.Assemble.FT.contDiff_dbarCoord_of hχ j)
      ((Work.NN.Assemble.FT.tsupport_dbarCoord_subset j).trans htsupp) (hη l i)
  have h3 : ContDiff ℝ 1 (fun w => dbarCoord l χ w * η j i w) :=
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_polydisc 0 r)
      (Work.NN.Assemble.FT.contDiff_dbarCoord_of hχ l)
      ((Work.NN.Assemble.FT.tsupport_dbarCoord_subset l).trans htsupp) (hη j i)
  exact (h1.add h2).sub h3

/-- `Edat χ η` is globally `C¹` when `tsupport χ ⊆ polydisc 0 r` and `η` is `C¹` there.
Parametric `Edat_contDiff_pd3`. -/
lemma tun_Edat_contDiff {n : ℕ} (hn : 0 < n) {r : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ polydisc 0 r)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 r)) (i m : Fin n) :
    ContDiff ℝ 1 (Work.NN.Assemble.FT.Edat χ η i m) := by
  rw [show Work.NN.Assemble.FT.Edat χ η i m = fun z =>
      (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
        * Work.CR.Flat.Cauchy.bmPot (fun j => Work.NN.Core.bmH χ η i m j) z from rfl]
  exact contDiff_const.mul (Work.NN.Assemble.FT.contDiff_bmPot (m := 1) hn
    (fun j => tun_contDiff_bmH hχ htsupp hη i m j)
    (fun j => Work.NN.Assemble.FT.bmH_hasCompactSupport hcs i m j))

/-- `Edat χ η` is antisymmetric when `η` is antisymmetric on `polydisc 0 r`.  Parametric
`Edat_antisymm_pd3`. -/
lemma tun_Edat_antisymm {n : ℕ} (hn : 0 < n) {r : Fin n → ℝ} {χ : (Fin n → ℂ) → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ polydisc 0 r)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 r))
    (hanti : ∀ i l z, z ∈ polydisc 0 r → η i l z = -η l i z) :
    ∀ j l z, Work.NN.Assemble.FT.Edat χ η j l z = - Work.NN.Assemble.FT.Edat χ η l j z := by
  intro j l z
  have hH : ∀ m w, Work.NN.Core.bmH χ η j l m w = - Work.NN.Core.bmH χ η l j m w :=
    fun m w => tun_bmH_antisymm htsupp hanti j l m w
  rw [Work.NN.Assemble.FT.Edat_apply, Work.NN.Assemble.FT.Edat_apply]
  have hpot : Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ η j l m) z
      = - Work.CR.Flat.Cauchy.bmPot (fun m => Work.NN.Core.bmH χ η l j m) z := by
    have hcong : (fun m => Work.NN.Core.bmH χ η j l m)
        = fun m y => - Work.NN.Core.bmH χ η l j m y := by
      funext m y; rw [hH m y]
    rw [hcong]
    have hcont : ∀ m : Fin n, Continuous (fun w => Work.NN.Core.bmH χ η l j m w) :=
      fun m => (tun_contDiff_bmH hχ htsupp hη l j m).continuous
    have hcs' : ∀ m : Fin n, HasCompactSupport (fun w => Work.NN.Core.bmH χ η l j m w) :=
      fun m => Work.NN.Assemble.FT.bmH_hasCompactSupport hcs l j m
    have h := congrFun (Work.NN.Assemble.FT.bmPot_real_smul hn (-1) hcont hcs') z
    simp only [Pi.smul_apply] at h
    have h2 : (fun m y => (↑(-1 : ℝ) : ℂ) * Work.NN.Core.bmH χ η l j m y)
        = fun m y => - Work.NN.Core.bmH χ η l j m y := by
      funext m y
      rw [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul]
    rw [h2] at h
    simpa [neg_one_smul] using h
  rw [hpot]; ring

/-- `Edat χ η` is `∂̄`-closed on `polydisc 0 S` when `χ` is supported in `polydisc 0 r ⊆ polydisc 0 R`,
equals `1` on a neighbourhood of the closed ball of radius `S` (`S < R` componentwise), and `η` is
`C¹` and closed on `polydisc 0 R`.  Parametric `Edat_closed_pd3`. -/
lemma tun_Edat_closed {n : ℕ} (hn : 0 < n) {r R S : Fin n → ℝ}
    (hrR : ∀ j, r j ≤ R j) (hSR : ∀ j, S j < R j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ polydisc 0 r)
    {V : Set (Fin n → ℂ)} (hVo : IsOpen V)
    (hKV : Set.univ.pi (fun i => Metric.closedBall (0 : ℂ) (S i)) ⊆ V)
    (hχ1 : ∀ y ∈ V, χ y = 1)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 R))
    (hcl : ∀ j l m z, z ∈ polydisc 0 R →
      dbarCoord j (η l m) z - dbarCoord l (η j m) z + dbarCoord m (η j l) z = 0) :
    ∀ j l m z, z ∈ polydisc 0 S →
      dbarCoord j (Work.NN.Assemble.FT.Edat χ η l m) z
        - dbarCoord l (Work.NN.Assemble.FT.Edat χ η j m) z
        + dbarCoord m (Work.NN.Assemble.FT.Edat χ η j l) z = 0 := by
  have htsuppR : tsupport χ ⊆ polydisc 0 R := htsupp.trans (polydisc_mono fun j => hrR j)
  intro j l m z hz
  have hzV : z ∈ V := hKV (by
    rw [Set.mem_univ_pi]
    intro i
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := hz i
    simp only [Pi.zero_apply, sub_zero] at h
    exact le_of_lt h)
  have hzeq : χ =ᶠ[nhds z] 1 := by
    filter_upwards [hVo.mem_nhds hzV] with w hw
    exact hχ1 w hw
  have hmain := Work.NN.Final.bmPot_bmH_dbarCoord_eq_local (n := n) hn
    (hχ.of_le (by simp)) hcs (isOpen_polydisc 0 R) htsuppR hη hcl j l m z
  have hmain0 : dbarCoord j
        (fun w => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η l m i) w) z
      - dbarCoord l
        (fun w => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j m i) w) z
      + dbarCoord m
        (fun w => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) w) z = 0 := by
    rw [hmain, Work.NN.Assemble.FT.bmH_eq_zero_of_eventuallyEq_one hzeq j l m, mul_zero]
  have hd : ∀ a b : Fin n, DifferentiableAt ℝ
      (fun w => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η a b i) w) z :=
    fun a b => Work.NN.Assemble.FT.differentiableAt_bmPot hn
      (fun i => tun_contDiff_bmH hχ htsuppR hη a b i)
      (fun i => Work.NN.Assemble.FT.bmH_hasCompactSupport hcs a b i) z
  rw [show Work.NN.Assemble.FT.Edat χ η l m
        = fun w => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
            * Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η l m i) w from rfl,
      show Work.NN.Assemble.FT.Edat χ η j m
        = fun w => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
            * Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j m i) w from rfl,
      show Work.NN.Assemble.FT.Edat χ η j l
        = fun w => (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
            * Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) w from rfl,
    Work.NN.Assemble.FT.dbarCoord_const_mul (j := j) _ _ z (hd l m),
    Work.NN.Assemble.FT.dbarCoord_const_mul (j := l) _ _ z (hd j m),
    Work.NN.Assemble.FT.dbarCoord_const_mul (j := m) _ _ z (hd j l)]
  linear_combination ((Work.CR.Flat.Cauchy.bmGamma n)⁻¹) * hmain0

/-- A three-fold `ofReal` reassociation in `ℝ≥0∞`. -/
lemma tun_ofReal_mul_three {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (S : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * (ENNReal.ofReal c * S))
      = ENNReal.ofReal (a * b * c) * S := by
  conv_lhs => rw [← mul_assoc, ← mul_assoc]
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul (mul_nonneg ha hb)]

/-- The double sum of `(n)²` copies of an `ofReal`-multiple. -/
lemma tun_sum_sum_ofReal_mul (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (S : ℝ≥0∞) :
    (∑ _i : Fin n, ∑ _m : Fin n, ENNReal.ofReal a * S)
      = ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * a)) * S := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast]
  rw [tun_ofReal_mul_three (a := (n : ℝ)) (b := (n : ℝ)) (c := a)
    (Nat.cast_nonneg n) (Nat.cast_nonneg n) ha]
  congr 1
  ring_nf

/-- The `C^{1,α}`-norm of `Edat χ η` on `polydisc 0 S` is controlled by the `C^{0,α}`-norm of `η`
on `polydisc 0 R`, when `tsupport χ ⊆ polydisc 0 r` with `r < R` and `S ≤ R`.
Parametric `Edat_gain_pd3`. -/
lemma tun_Edat_gain {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {r R T : Fin n → ℝ} (hRpos : ∀ j, 0 < R j) (hrR : ∀ j, r j < R j)
    (hTR : ∀ j, T j ≤ R j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ polydisc 0 r) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : Fin n → Fin n → (Fin n → ℂ) → ℂ,
      (∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 R)) → ∀ j l : Fin n,
        holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η j l) (polydisc 0 T)
          ≤ ENNReal.ofReal C * ∑ a : Fin n, ∑ b : Fin n,
              holderNorm 0 α (η a b) (polydisc 0 R) := by
  have htsuppR : tsupport χ ⊆ polydisc 0 R := htsupp.trans (polydisc_mono fun j => le_of_lt (hrR j))
  obtain ⟨Ch, hChpos, hCh⟩ :=
    tun_bmH (α := α) (le_of_lt hα0) (le_of_lt hα1) (r := r) (R := R) hrR hχ hcs htsupp
  obtain ⟨Cg, hCgpos, hCg⟩ := Work.NN.Core.bmPotential_gain (n := n) hn hα0 hα1
    (ρ := R) hRpos 0
  refine ⟨‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg * ((n : ℝ) * Ch) + 1, by positivity, ?_⟩
  intro η hη j l
  have hη0 : ∀ i m : Fin n, ContDiffOn ℝ (0 : ℕ∞) (η i m) (polydisc 0 R) :=
    fun i m => (hη i m).of_le (by norm_num)
  set S : ℝ≥0∞ := ∑ a : Fin n, ∑ b : Fin n,
    holderNorm 0 α (η a b) (polydisc 0 R) with hSdef
  have hg1 : ∀ i : Fin n, ContDiff ℝ 1 (fun w => Work.NN.Core.bmH χ η j l i w) :=
    fun i => tun_contDiff_bmH hχ htsuppR hη j l i
  have hgcs : ∀ i : Fin n, HasCompactSupport (fun w => Work.NN.Core.bmH χ η j l i w) :=
    fun i => Work.NN.Assemble.FT.bmH_hasCompactSupport hcs j l i
  have hgfin : ∀ i : Fin n,
      holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ < ⊤ :=
    fun i => Work.NN.Core.holderNorm_zero_univ_lt_top_of_contDiff_one hα0 hα1 (hg1 i) (hgcs i)
  have hgsup : ∀ i : Fin n, ∀ z, (∃ m, R m ≤ ‖z m‖) →
      Work.NN.Core.bmH χ η j l i z = 0 := by
    intro i z hz
    obtain ⟨m, hm⟩ := hz
    have hzm : z ∉ polydisc 0 r := by
      intro h
      have h1 : ‖z m‖ < r m := by simpa only [Pi.zero_apply, sub_zero] using h m
      linarith [lt_of_lt_of_le h1 (le_of_lt (hrR m))]
    have h0 : ∀ a : Fin n, dbarCoord a χ z = 0 := fun a => by
      by_contra hne
      exact hzm (htsupp (Work.NN.Assemble.FT.tsupport_dbarCoord_subset a
        (subset_tsupport _ (Function.mem_support.mpr hne))))
    rw [Work.NN.Assemble.FT.bmH_eq_sum, h0 i, h0 j, h0 l]; ring
  obtain ⟨hcd, hest⟩ := hCg (fun i => fun w => Work.NN.Core.bmH χ η j l i w)
    (fun i => (hg1 i).of_le (by norm_num)) hgcs hgfin hgsup
  have hbmP : (fun z => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z)
      = fun z => Work.CR.Flat.Cauchy.bmPotential (fun i => Work.NN.Core.bmH χ η j l i) z :=
    funext fun z => (Work.CR.Flat.Cauchy.bmPotential_eq_bmPot _ z).symm
  have hsum : (∑ i : Fin n,
        holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ)
      ≤ ENNReal.ofReal ((n : ℝ) * Ch) * S := by
    calc (∑ i : Fin n,
            holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ)
        ≤ ∑ _i : Fin n, (ENNReal.ofReal Ch * S) :=
          Finset.sum_le_sum fun i _ => by rw [hSdef]; exact hCh η hη0 j l i
      _ = (n : ℝ≥0∞) * (ENNReal.ofReal Ch * S) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = ENNReal.ofReal ((n : ℝ) * Ch) * S := by
          rw [← ENNReal.ofReal_natCast, ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  have hEdat : Work.NN.Assemble.FT.Edat χ η j l
      = (Work.CR.Flat.Cauchy.bmGamma n)⁻¹
        • (fun z => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z) := by
    funext z; rw [Work.NN.Assemble.FT.Edat_apply]; rfl
  calc holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η j l) (polydisc 0 T)
      ≤ holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η j l) (polydisc 0 R) :=
        holderNorm_mono_set (isOpen_polydisc 0 R) (isOpen_polydisc 0 T)
          (polydisc_mono (fun j => hTR j)) 1 α _
    _ = ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * holderNorm 1 α
              (fun z => Work.CR.Flat.Cauchy.bmPot (fun i => Work.NN.Core.bmH χ η j l i) z)
              (polydisc 0 R) := by
        rw [hEdat]
        exact Work.CR.Flat.Holder.holderNorm_smul _ (by rw [hbmP]; exact hcd)
          (isOpen_polydisc 0 R).uniqueDiffOn
    _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * (ENNReal.ofReal Cg * (∑ i : Fin n,
              holderNorm 0 α (fun w => Work.NN.Core.bmH χ η j l i w) Set.univ)) := by
        refine mul_le_mul' le_rfl ?_
        rw [hbmP]
        exact hest
    _ ≤ ENNReal.ofReal ‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖
          * (ENNReal.ofReal Cg * (ENNReal.ofReal ((n : ℝ) * Ch) * S)) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hsum)
    _ = ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg * ((n : ℝ) * Ch)) * S :=
        tun_ofReal_mul_three (norm_nonneg _) (le_of_lt hCgpos) (mul_nonneg (Nat.cast_nonneg n)
          (le_of_lt hChpos)) S
    _ ≤ ENNReal.ofReal (‖(Work.CR.Flat.Cauchy.bmGamma n)⁻¹‖ * Cg * ((n : ℝ) * Ch) + 1) * S :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal (by linarith)) _


/-! ### The Bochner–Martinelli defect identity, parametrically -/

/-- **Parametric `(0,2)`-defect identity of one Bochner–Martinelli step.**  If `χ` is smooth and
compactly supported in `polydisc 0 r`, equals `1` on an open set `V` containing the closed ball of
multi-radius `r₁` (with `r ≤ R` and `r₁ < R` componentwise), and `η` is `C¹` and `∂̄`-closed on
`polydisc 0 R`, then for `z ∈ polydisc 0 r₁`
`∂̄_j (bmRow (χ·η) l) z - ∂̄_l (bmRow (χ·η) j) z = η j l z + bmDefect χ η j l z`.
Parametric `bmDefect_eq_pd83`. -/
lemma tun_bmDefect {n : ℕ} (hn : 0 < n) {r r₁ R : Fin n → ℝ}
    (hRpos : ∀ j, 0 < R j) (hrR : ∀ j, r j ≤ R j) (hr₁R : ∀ j, r₁ j < R j)
    {χ : (Fin n → ℂ) → ℂ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcs : HasCompactSupport χ)
    (htsupp : tsupport χ ⊆ polydisc 0 r)
    {V : Set (Fin n → ℂ)} (hVo : IsOpen V)
    (hKV : Set.univ.pi (fun i => Metric.closedBall (0 : ℂ) (r₁ i)) ⊆ V)
    (hχ1 : ∀ y ∈ V, χ y = 1)
    {η : Fin n → Fin n → (Fin n → ℂ) → ℂ}
    (hη : ∀ i l, ContDiffOn ℝ 1 (η i l) (polydisc 0 R))
    (hcl : ∀ j l m z, z ∈ polydisc 0 R →
      dbarCoord j (η l m) z - dbarCoord l (η j m) z + dbarCoord m (η j l) z = 0) :
    ∀ j l z, z ∈ polydisc 0 r₁ →
      dbarCoord j (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) l) z
        - dbarCoord l (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) z
      = η j l z + Work.NN.Core.bmDefect χ η j l z := by
  have htsuppR : tsupport χ ⊆ polydisc 0 R := htsupp.trans (polydisc_mono fun j => hrR j)
  have hK'c : IsCompact (tsupport χ ∪
      Set.univ.pi fun i => Metric.closedBall (0 : ℂ) (r₁ i)) :=
    hcs.isCompact.union (isCompact_univ_pi fun i => isCompact_closedBall 0 _)
  have hK'U : (tsupport χ ∪
      Set.univ.pi fun i => Metric.closedBall (0 : ℂ) (r₁ i)) ⊆ polydisc 0 R := by
    intro z hz
    rcases hz with hz | hz
    · exact htsuppR hz
    · rw [tun_mem_polydisc_zero]; intro i
      have h2 : ‖z i‖ ≤ r₁ i := by
        have h := hz i; rw [Metric.mem_closedBall, dist_eq_norm] at h; simpa using h
      have h3 : r₁ i < R i := hr₁R i
      linarith
  obtain ⟨χ₂, W, hχ₂, _hcs₂, htsupp₂, hWo, hKW, hχ₂1⟩ :=
    Work.NN.Core.exists_contDiff_bump_of_isCompact_subset hK'c (isOpen_polydisc 0 R) hK'U
  have hWK : tsupport χ ⊆ W := fun z hz => hKW (Or.inl hz)
  have hUopen : IsOpen (W ∩ polydisc 0 R) := hWo.inter (isOpen_polydisc 0 R)
  have hχU : ∀ z, χ z ≠ 0 → z ∈ W ∩ polydisc 0 R := fun z hz =>
    ⟨hWK (subset_tsupport χ (Function.mem_support.mpr hz)),
      htsuppR (subset_tsupport χ (Function.mem_support.mpr hz))⟩
  set η₂ : Fin n → Fin n → (Fin n → ℂ) → ℂ := fun i l w => χ₂ w * η i l w with hη₂def
  have hη₂diff : ∀ i l, ContDiff ℝ 1 (η₂ i l) := fun i l =>
    Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_polydisc 0 R) hχ₂ htsupp₂
      (hη i l)
  have hη₂closed : ∀ j l m z, z ∈ W ∩ polydisc 0 R →
      dbarCoord j (η₂ l m) z - dbarCoord l (η₂ j m) z
        + dbarCoord m (η₂ j l) z = 0 := by
    intro j l m z hz
    have hder : ∀ a b : Fin n, fderiv ℝ (fun w => χ₂ w * η a b w) z = fderiv ℝ (η a b) z := by
      intro a b
      have h1 : (fun w => χ₂ w * η a b w) =ᶠ[nhds z] (η a b) := by
        filter_upwards [hWo.mem_nhds hz.1] with w hw
        rw [hχ₂1 w hw, one_mul]
      exact h1.fderiv_eq
    have e1 : dbarCoord j (η₂ l m) z = dbarCoord j (η l m) z := by
      simp only [hη₂def, dbarCoord, hder l m]
    have e2 : dbarCoord l (η₂ j m) z = dbarCoord l (η j m) z := by
      simp only [hη₂def, dbarCoord, hder j m]
    have e3 : dbarCoord m (η₂ j l) z = dbarCoord m (η j l) z := by
      simp only [hη₂def, dbarCoord, hder j l]
    rw [e1, e2, e3]
    exact hcl j l m z hz.2
  obtain ⟨R₀, hR₀pos, hR₀⟩ := hcs.isCompact.isBounded.exists_pos_norm_le
  have hgl := Work.NN.Final.bmDefect_eq_local (n := n) hn (R := R₀ + 1) (by linarith)
    (U := W ∩ polydisc 0 R) hUopen χ (hχ.of_le (by simp))
    (fun z hz => by
      by_contra hc
      have hmem : z ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hc)
      linarith [hR₀ z hmem])
    hχU η₂ hη₂diff hη₂closed
  have hprod : ∀ i l' : Fin n, (fun w => χ w * η₂ i l' w) = fun w => χ w * η i l' w := by
    intro i l'
    funext w
    by_cases hc : χ w = 0
    · rw [hc, zero_mul, zero_mul]
    · have hmem : w ∈ tsupport χ := subset_tsupport χ (Function.mem_support.mpr hc)
      simp only [hη₂def]
      rw [hχ₂1 w (hWK hmem), one_mul]
  have hrow : ∀ i : Fin n, Work.NN.Core.bmRow (fun a b w => χ w * η₂ a b w) i
      = Work.NN.Core.bmRow (fun a b w => χ w * η a b w) i := by
    intro i
    have hfg : (fun a b w => χ w * η₂ a b w) = fun a b w => χ w * η a b w := by
      funext a b w; exact congrFun (hprod a b) w
    rw [hfg]
  have hH : ∀ i l' m' w, Work.NN.Core.bmH χ η₂ i l' m' w = Work.NN.Core.bmH χ η i l' m' w := by
    intro i l' m' w
    rw [Work.NN.Assemble.FT.bmH_eq_sum, Work.NN.Assemble.FT.bmH_eq_sum]
    by_cases hw : w ∈ tsupport χ
    · have h1 : η₂ i l' w = η i l' w := by
        simp only [hη₂def]; rw [hχ₂1 w (hWK hw), one_mul]
      have h2 : η₂ l' m' w = η l' m' w := by
        simp only [hη₂def]; rw [hχ₂1 w (hWK hw), one_mul]
      have h3 : η₂ i m' w = η i m' w := by
        simp only [hη₂def]; rw [hχ₂1 w (hWK hw), one_mul]
      rw [h1, h2, h3]
    · have h0 : χ =ᶠ[nhds w] 0 := by
        filter_upwards [(isClosed_tsupport χ).compl_mem_nhds hw] with y hy
        exact Function.notMem_support.mp fun hy' => hy (subset_tsupport χ hy')
      have hfd : fderiv ℝ χ w = 0 := by
        have h := h0.fderiv_eq (𝕜 := ℝ)
        simpa using h
      have hdb : ∀ a : Fin n, dbarCoord a χ w = 0 :=
        fun a => by simp [dbarCoord, hfd]
      rw [hdb m', hdb i, hdb l']
      ring
  intro j l z hz
  have hχ₂z : χ₂ z = 1 := hχ₂1 z (hKW (Or.inr (by
    rw [Set.mem_univ_pi]; intro i
    rw [Metric.mem_closedBall, dist_zero_right]
    have h := hz i
    simp only [Pi.zero_apply, sub_zero] at h
    exact le_of_lt h)))
  have hzj : η₂ j l z = η j l z := by simp only [hη₂def]; rw [hχ₂z, one_mul]
  have hdefz : Work.NN.Core.bmDefect χ η₂ j l z = Work.NN.Core.bmDefect χ η j l z := by
    rw [Work.NN.Core.bmDefect_apply, Work.NN.Core.bmDefect_apply]
    have hF : (fun m' => Work.NN.Core.bmH χ η₂ j l m')
        = fun m' => Work.NN.Core.bmH χ η j l m' := by
      funext m' w; exact hH j l m' w
    rw [hzj, hF]
  have hj := hgl j l z
  rw [hrow j, hrow l] at hj
  rw [hj, hzj, hdefz]

/-! ## The tunable-loss `(0,2)`-solver -/

set_option maxHeartbeats 2000000 in
theorem flatTwoTunable {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {c : ℝ} (hc : 1 < c) : ∃ C : ℝ, 0 < C ∧ ∃ T2 : (Fin n → Fin n → Work.NN.Core.Cn n → ℂ) → (Fin n → Work.NN.Core.Cn n → ℂ), (∀ η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ, (∀ j l, ContDiffOn ℝ (1 : ℕ∞) (η j l) (Work.CR.Flat.polydisc 0 (fun i => c * ρ i))) → (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 (fun i => c * ρ i) → η j l z = - η l j z) → Work.NN.Final.Clos2 n ρ c η → ∀ (j l : Fin n) (z : Work.NN.Core.Cn n), z ∈ Work.CR.Flat.polydisc 0 ρ → Work.CR.Flat.dbarCoord j (T2 η l) z - Work.CR.Flat.dbarCoord l (T2 η j) z = η j l z) ∧ (∀ η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ, (∀ j l, ContDiffOn ℝ (1 : ℕ∞) (η j l) (Work.CR.Flat.polydisc 0 (fun i => c * ρ i))) → (∀ j l z, z ∈ Work.CR.Flat.polydisc 0 (fun i => c * ρ i) → η j l z = - η l j z) → Work.NN.Final.Clos2 n ρ c η → ∀ j : Fin n, Work.CR.Flat.holderNorm 1 α (T2 η j) (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal C * ∑ j, ∑ l, Work.CR.Flat.holderNorm 0 α (η j l) (Work.CR.Flat.polydisc 0 (fun i => c * ρ i))) := by
  by_cases hn1 : n = 1
  · subst hn1
    refine ⟨1, one_pos, fun _ => 0, ?_, ?_⟩
    · intro η hη hanti hcl j l z hz
      have hjl : j = l := Subsingleton.elim j l
      have h0 : η j l z = 0 := by
        rw [hjl]
        have hmem : z ∈ Work.CR.Flat.polydisc (0 : Fin 1 → ℂ) (fun i => c * ρ i) := by
          rw [tun_mem_polydisc_zero]
          intro i
          rw [tun_mem_polydisc_zero] at hz
          have hp := hρ i
          have h := hz i
          nlinarith [h, hp, hc]
        have h := hanti l l z hmem
        linear_combination (1 / 2 : ℂ) * h
      rw [h0]
      simp [Work.CR.Flat.dbarCoord]
    · intro η hη hanti hcl j
      have hz0 : Work.CR.Flat.holderNorm 1 α
          ((fun _ : Fin 1 → Fin 1 → Work.NN.Core.Cn 1 → ℂ =>
            (0 : Fin 1 → Work.NN.Core.Cn 1 → ℂ)) η j)
          (Work.CR.Flat.polydisc (0 : Fin 1 → ℂ) ρ) = 0 := by
        simp [Work.CR.Flat.holderNorm, Work.CR.Flat.iterDerivNorm, Work.CR.Flat.holderSeminorm]
      rw [hz0]
      exact bot_le
  · have hρc : ∀ j, 0 < c * ρ j := fun j => by have h := hρ j; nlinarith
    set c₂ : ℝ := (1 + c) / 2 with hc₂def
    set c₁ : ℝ := (1 + c₂) / 2 with hc₁def
    have hc₁1 : 1 < c₁ := by rw [hc₁def, hc₂def]; linarith
    have hc₁c₂ : c₁ < c₂ := by rw [hc₁def]; linarith
    have hc₂c : c₂ < c := by rw [hc₂def]; linarith
    have hρ₂ : ∀ j, 0 < c₂ * ρ j := fun j => by have h := hρ j; nlinarith
    have hρ₁ : ∀ j, 0 < c₁ * ρ j := fun j => by have h := hρ j; nlinarith
    have hKc : IsCompact (Set.univ.pi fun i => Metric.closedBall (0 : ℂ) (c₁ * ρ i)) :=
      isCompact_univ_pi fun i => isCompact_closedBall 0 _
    have hKU : (Set.univ.pi fun i => Metric.closedBall (0 : ℂ) (c₁ * ρ i)) ⊆ pd n ρ c₂ := by
      intro z hz
      rw [mem_pd]
      intro i
      have h := hz i
      rw [Metric.mem_closedBall, dist_eq_norm] at h
      have h1 : ‖z i‖ ≤ c₁ * ρ i := by simpa using h
      have h2 : c₁ * ρ i < c₂ * ρ i := by have hp := hρ i; nlinarith
      linarith
    obtain ⟨χ, V, hχ, hcs, htsupp, hVo, hKV, hχ1⟩ :=
      Work.NN.Core.exists_contDiff_bump_of_isCompact_subset hKc (isOpen_pd ρ c₂) hKU
    have htsuppc : tsupport χ ⊆ pd n ρ c := htsupp.trans (pd_mono hρ (le_of_lt hc₂c))
    obtain ⟨T, CT, hCTpos, hTsol, hTest, hTsm, hTreg⟩ :=
      Work.NN.Core.exists_telTwoDF_smooth (n := n) (α := α) hα0 hα1
        (ρ := fun i => c₁ * ρ i) (ρ' := ρ) hρ₁ hρ (fun i => by have h := hρ i; nlinarith)
    obtain ⟨Cb, hCbpos, hCb⟩ := Work.NN.Core.bmRow_holder (n := n) hn hα0 hα1
      (c := 0) (r := fun i => (2 * c) * ρ i) (fun i => by have h := hρ i; nlinarith) 0
    obtain ⟨Cc, hCcpos, hCc⟩ := tun_chiMul (α := α) (r := fun i => c₂ * ρ i)
      (R := fun i => c * ρ i) hα0.le hα1.le (fun i => by have h := hρ i; nlinarith)
      hχ hcs htsupp 0
    obtain ⟨Ce, hCepos, hCe⟩ := tun_Edat_gain (n := n) hn hα0 hα1 (r := fun i => c₂ * ρ i)
      (R := fun i => c * ρ i) (T := fun i => c₁ * ρ i) hρc (fun i => by have h := hρ i; nlinarith)
      (fun i => by have h := hρ i; nlinarith) hχ hcs htsupp
    have hCpos : 0 < Cb * Cc + CT 1 * ((n : ℝ) * ((n : ℝ) * Ce)) + 1 := by
      have h1 := hCbpos; have h2 := hCcpos; have h3 := hCTpos 1; have h4 := hCepos
      have h5 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      positivity
    refine ⟨Cb * Cc + CT 1 * ((n : ℝ) * ((n : ℝ) * Ce)) + 1, hCpos,
      fun η => Work.NN.Core.bmRow (fun a b w => χ w * η a b w)
        + T (Work.NN.Assemble.FT.Edat χ η), ?_, ?_⟩
    · -- the equation
      intro η hη hanti hcl j l z hz
      have hη' : ∀ i m, ContDiffOn ℝ 1 (η i m) (pd n ρ c) := fun i m => hη i m
      have hcl' : ∀ i m m' w, w ∈ pd n ρ c →
          dbarCoord i (η m m') w - dbarCoord m (η i m') w
            + dbarCoord m' (η i m) w = 0 := fun i m m' w hw => hcl i m m' w hw
      have hKV1 : Set.univ.pi (fun i => Metric.closedBall (0 : ℂ) (ρ i)) ⊆ V := by
        intro z hz2
        refine hKV ?_
        rw [Set.mem_univ_pi] at hz2 ⊢
        intro i
        have h := hz2 i
        rw [Metric.mem_closedBall, dist_eq_norm] at h ⊢
        have h1 : ‖z i‖ ≤ ρ i := by simpa using h
        have h2 : ρ i ≤ c₁ * ρ i := by have hp := hρ i; nlinarith
        simpa using le_trans h1 h2
      have hdef := tun_bmDefect (n := n) hn (r := fun i => c₂ * ρ i) (r₁ := ρ)
        (R := fun i => c * ρ i) hρc (fun i => by have h := hρ i; nlinarith)
        (fun i => by have h := hρ i; nlinarith) hχ hcs htsupp hVo hKV1 hχ1 hη' hcl' j l z hz
      have hEd1 : ∀ i m : Fin n,
          ContDiffOn ℝ 1 (Work.NN.Assemble.FT.Edat χ η i m)
            (polydisc 0 (fun i => c₁ * ρ i)) :=
        fun i m => (tun_Edat_contDiff hn hχ hcs htsuppc hη' i m).contDiffOn
      have hEanti : Work.NN.Core.IsAntisymmTwo (Work.NN.Assemble.FT.Edat χ η) :=
        fun i m w => tun_Edat_antisymm hn hχ hcs htsuppc hη' hanti i m w
      have hEcl : Work.NN.Core.IsClosedTwoOn (fun i => c₁ * ρ i)
          (Work.NN.Assemble.FT.Edat χ η) :=
        fun i m m' w hw => tun_Edat_closed hn (r := fun i => c₂ * ρ i) (R := fun i => c * ρ i)
          (S := fun i => c₁ * ρ i) (fun j => le_of_lt (by have h := hρ j; nlinarith))
          (fun j => by have h := hρ j; nlinarith) hχ hcs htsupp hVo hKV hχ1 hη' hcl' i m m' w hw
      have hTs := hTsol (Work.NN.Assemble.FT.Edat χ η) hEd1 hEanti hEcl j l z hz
      have hbm : Work.NN.Core.bmDefect χ η j l z = - Work.NN.Assemble.FT.Edat χ η j l z := by
        rw [Work.NN.Core.bmDefect_apply, Work.NN.Assemble.FT.Edat_apply]
        have hχz : χ z = 1 := hχ1 z (hKV (by
          rw [Set.mem_univ_pi]
          intro i
          rw [Metric.mem_closedBall, dist_zero_right]
          rw [tun_mem_polydisc_zero] at hz
          have h := hz i
          have h2 : ρ i ≤ c₁ * ρ i := by have hp := hρ i; nlinarith
          linarith))
        rw [hχz]; ring
      have hglob : ∀ a b : Fin n, ContDiff ℝ 1 (fun w => χ w * η a b w) := fun a b =>
        Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ c) hχ htsuppc
          (hη' a b)
      have hAd : ∀ i : Fin n, DifferentiableAt ℝ
          (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) i) z := fun i =>
        Work.NN.Assemble.FT.differentiableAt_bmRow hn
          (fun a b => hglob a b) (fun a b => hcs.mul_right) i z
      have hTd : ∀ i : Fin n, DifferentiableAt ℝ (T (Work.NN.Assemble.FT.Edat χ η) i) z :=
        fun i => ((hTreg 1 (Work.NN.Assemble.FT.Edat χ η) hEd1 i).contDiffAt
          ((isOpen_polydisc (0 : Fin n → ℂ) ρ).mem_nhds hz)).differentiableAt one_ne_zero
      rw [hbm] at hdef
      show Work.CR.Flat.dbarCoord j (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) l
            + T (Work.NN.Assemble.FT.Edat χ η) l) z
          - Work.CR.Flat.dbarCoord l (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j
            + T (Work.NN.Assemble.FT.Edat χ η) j) z = η j l z
      rw [Work.NN.Assemble.FT.dbarCoord_add_pi j (hAd l) (hTd l),
          Work.NN.Assemble.FT.dbarCoord_add_pi l (hAd j) (hTd j)]
      linear_combination hdef + hTs
    · -- the estimate
      intro η hη hanti hcl j
      have hη' : ∀ i m, ContDiffOn ℝ 1 (η i m) (pd n ρ c) := fun i m => hη i m
      have hcl' : ∀ i m m' w, w ∈ pd n ρ c →
          dbarCoord i (η m m') w - dbarCoord m (η i m') w
            + dbarCoord m' (η i m) w = 0 := fun i m m' w hw => hcl i m m' w hw
      set S : ℝ≥0∞ := ∑ j : Fin n, ∑ l : Fin n, Work.CR.Flat.holderNorm 0 α (η j l)
        (Work.CR.Flat.polydisc 0 (fun i => c * ρ i)) with hSdef
      by_cases htop : S = ⊤
      · rw [htop, ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; positivity)]
        exact le_top
      · have hglob : ∀ a b : Fin n, ContDiff ℝ 1 (fun w => χ w * η a b w) := fun a b =>
          Work.NN.Final.contDiff_mul_of_contDiffOn_tsupport (m := 1) (isOpen_pd ρ c) hχ htsuppc
            (hη' a b)
        have hEd1 : ∀ i m : Fin n,
            ContDiffOn ℝ 1 (Work.NN.Assemble.FT.Edat χ η i m)
              (polydisc 0 (fun i => c₁ * ρ i)) :=
          fun i m => (tun_Edat_contDiff hn hχ hcs htsuppc hη' i m).contDiffOn
        have hEanti : Work.NN.Core.IsAntisymmTwo (Work.NN.Assemble.FT.Edat χ η) :=
          fun i m w => tun_Edat_antisymm hn hχ hcs htsuppc hη' hanti i m w
        have hEcl : Work.NN.Core.IsClosedTwoOn (fun i => c₁ * ρ i)
            (Work.NN.Assemble.FT.Edat χ η) :=
          fun i m m' w hw => tun_Edat_closed hn (r := fun i => c₂ * ρ i) (R := fun i => c * ρ i)
            (S := fun i => c₁ * ρ i) (fun j => le_of_lt (by have h := hρ j; nlinarith))
            (fun j => by have h := hρ j; nlinarith) hχ hcs htsupp hVo hKV hχ1 hη' hcl'
            i m m' w hw
        have hvan : ∀ a b (w : Fin n → ℂ),
            (∃ i, ((2 * c) * ρ i) / 2 ≤ ‖w i - (0 : Fin n → ℂ) i‖) → χ w * η a b w = 0 := by
          intro a b w hw
          obtain ⟨i, hi⟩ := hw
          simp only [Pi.zero_apply, sub_zero] at hi
          have hwi : c * ρ i ≤ ‖w i‖ := by linarith [hi]
          have hnot : w ∉ pd n ρ c := fun h => by
            have h1 := mem_pd.mp h i
            linarith
          have hχ0 : χ w = 0 := by
            by_contra hc0
            exact hnot (htsuppc (subset_tsupport χ (Function.mem_support.mpr hc0)))
          rw [hχ0, zero_mul]
        have hset : polydisc (0 : Fin n → ℂ) (fun i => ((2 * c) * ρ i) / 2) = pd n ρ c := by
          have hfun : (fun i : Fin n => ((2 * c) * ρ i) / 2) = fun i : Fin n => c * ρ i := by
            funext i; ring
          rw [hfun]; rfl
        have hbmEst : Work.CR.Flat.holderNorm 1 α
            (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ)
            ≤ ENNReal.ofReal (Cb * Cc) * S := by
          have hcb := hCb (fun a b w => χ w * η a b w) (fun a b => hglob a b) hvan j
          rw [hset] at hcb
          have hsumC : (∑ m : Fin n, ∑ m' : Fin n,
                Work.CR.Flat.holderNorm 0 α (fun w => χ w * η m m' w) Set.univ)
              ≤ ENNReal.ofReal Cc * S := by
            rw [hSdef, Finset.mul_sum]
            refine Finset.sum_le_sum fun m _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_le_sum fun m' _ => hCc (η m m') ((hη' m m').of_le (by norm_num))
          calc Work.CR.Flat.holderNorm 1 α
                (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (polydisc 0 ρ)
              ≤ Work.CR.Flat.holderNorm 1 α
                  (Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j) (pd n ρ c) :=
                Work.CR.Flat.holderNorm_mono_set (isOpen_pd ρ c) (isOpen_polydisc 0 ρ)
                  (polydisc_mono (fun i => by have h := hρ i; nlinarith)) 1 α _
            _ ≤ ENNReal.ofReal Cb * (∑ m : Fin n, ∑ m' : Fin n,
                  Work.CR.Flat.holderNorm 0 α (fun w => χ w * η m m' w) Set.univ) := hcb
            _ ≤ ENNReal.ofReal Cb * (ENNReal.ofReal Cc * S) := mul_le_mul' le_rfl hsumC
            _ = ENNReal.ofReal (Cb * Cc) * S := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt hCbpos)]
        have hsumE : (∑ i : Fin n, ∑ m : Fin n,
              Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η i m)
                (polydisc 0 (fun i => c₁ * ρ i)))
            ≤ ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * Ce)) * S := by
          have hle : (∑ i : Fin n, ∑ m : Fin n,
                Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η i m)
                  (polydisc 0 (fun i => c₁ * ρ i)))
              ≤ ∑ _i : Fin n, ∑ _m : Fin n, (ENNReal.ofReal Ce * S) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun m _ => by
              rw [hSdef]; exact hCe η hη' i m
          refine hle.trans (le_of_eq ?_)
          exact tun_sum_sum_ofReal_mul n (le_of_lt hCepos) S
        have hTest' : Work.CR.Flat.holderNorm 1 α (T (Work.NN.Assemble.FT.Edat χ η) j)
              (polydisc 0 ρ)
            ≤ ENNReal.ofReal (CT 1 * ((n : ℝ) * ((n : ℝ) * Ce))) * S := by
          have ht := hTest 1 (Work.NN.Assemble.FT.Edat χ η) hEd1 hEanti hEcl j
          calc Work.CR.Flat.holderNorm 1 α (T (Work.NN.Assemble.FT.Edat χ η) j) (polydisc 0 ρ)
              ≤ ENNReal.ofReal (CT 1) * (∑ i : Fin n, ∑ m : Fin n,
                  Work.CR.Flat.holderNorm 1 α (Work.NN.Assemble.FT.Edat χ η i m)
                    (polydisc 0 (fun i => c₁ * ρ i))) := ht
            _ ≤ ENNReal.ofReal (CT 1)
                  * (ENNReal.ofReal ((n : ℝ) * ((n : ℝ) * Ce)) * S) :=
                mul_le_mul' le_rfl hsumE
            _ = ENNReal.ofReal (CT 1 * ((n : ℝ) * ((n : ℝ) * Ce))) * S := by
                rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (hCTpos 1))]
        have hsplit := Work.CR.Flat.Holder.holderNorm_add_le
          (f := Work.NN.Core.bmRow (fun a b w => χ w * η a b w) j)
          (g := T (Work.NN.Assemble.FT.Edat χ η) j)
          (Ω := polydisc 0 ρ) (α := α)
          (Work.NN.Assemble.FT.contDiff_bmRow hn (fun a b => hglob a b)
            (fun a b => hcs.mul_right) j).contDiffOn
          (hTreg 1 (Work.NN.Assemble.FT.Edat χ η) hEd1 j)
          (isOpen_polydisc (0 : Fin n → ℂ) ρ).uniqueDiffOn
        have harith : ENNReal.ofReal (Cb * Cc) * S
              + ENNReal.ofReal (CT 1 * ((n : ℝ) * ((n : ℝ) * Ce))) * S
            = ENNReal.ofReal (Cb * Cc + CT 1 * ((n : ℝ) * ((n : ℝ) * Ce))) * S := by
          have g1 : (0 : ℝ) ≤ Cb * Cc := le_of_lt (mul_pos hCbpos hCcpos)
          have g2 : (0 : ℝ) ≤ CT 1 * ((n : ℝ) * ((n : ℝ) * Ce)) :=
            mul_nonneg (le_of_lt (hCTpos 1))
              (mul_nonneg (Nat.cast_nonneg n) (mul_nonneg (Nat.cast_nonneg n) (le_of_lt hCepos)))
          rw [← add_mul, ← ENNReal.ofReal_add g1 g2]
        refine (hsplit.trans (add_le_add hbmEst hTest')).trans ?_
        rw [harith]
        refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (bot_le)
        linarith [le_of_lt (hCTpos 1)]

end

end Work.NN.Final
