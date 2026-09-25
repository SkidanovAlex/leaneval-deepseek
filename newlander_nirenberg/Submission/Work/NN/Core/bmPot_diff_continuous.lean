/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Differentiability of the Bochner–Martinelli potential of `C^{0,α}` data

The Bochner–Martinelli potential `bmPotential f z = Σ_j ∫ \overline{ζ_j - z_j} f_j(ζ)/‖ζ-z‖^{2n} dζ`
gains one derivative: for `0 < α < 1` and data `g` whose components are bounded and `α`-Hölder on
`ℂⁿ` and vanish off the half-size polydisc `polydisc c (r/2)`, the potential is (real) differentiable
at every point of `polydisc c (r/2)`.

The proof is the differentiability half of the `C^{1,α}` Schauder estimate
(`Work.NN.Core.bmPot_holder_C0a`): the data are approximated by their smooth mollifications
(`Work.NN.Core.bmSmoothApprox`, keeping the support and the `C^{0,α}` bounds), the derivative of the
potential of smooth data is the explicit singular integral `Work.NN.Core.bmDerivData` involving only
the *values* of the data (`Work.NN.Core.fderiv_bmPot_eq_bmDerivData`), those candidate derivatives
converge (`Work.NN.Core.tendsto_bmDerivData_apply`), and a uniform `‖h‖^{1+α}` Taylor bound for the
approximations passes to the limit.
-/
import Mathlib
import Submission.Work.NN.Core.bmPot_holder_C0a

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set Filter

namespace Work.NN.Core

open Work.CR.Flat
open Work.CR.Flat.Cauchy

theorem bmPot_diff_continuous {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {r : Fin n → ℝ}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (hr : ∀ j, 0 < r j)
    {g : Fin n → (Fin n → ℂ) → ℂ} (hg : ∀ j, Continuous (g j))
    (hgfin : ∀ j, Work.CR.Flat.holderNorm 0 α (g j) Set.univ < ⊤)
    (hgsup : ∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → g j z = 0) :
    ∀ z ∈ Work.CR.Flat.polydisc c (fun j => r j / 2),
      DifferentiableAt ℝ (fun z => Work.CR.Flat.Cauchy.bmPotential g z) z := by
  have hgsupp : ∀ j z, (∃ i, r i / 2 ≤ ‖z i - c i‖) → g j z = 0 := hgsup
  classical
  obtain ⟨C₁, hC₁pos, hC₁⟩ := bmPotential_holder hn (c := c) (r := fun j => 2 * r j) hα hα1
    (fun j => by linarith [hr j])
  obtain ⟨cc, hcc⟩ := bmCz.integral_bmKernel_mul_dbarCoord hn
  set Rb : ℝ := 2 * Real.sqrt n * ((∑ j, r j) + ‖c‖ + 1) with hRbdef
  have hRbpos : 0 < Rb := by
    rw [hRbdef]
    have h1 : 0 < ∑ j, r j := Finset.sum_pos (fun j _ => hr j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
    have h2 : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have h3 : 0 ≤ ‖c‖ := norm_nonneg c
    positivity
  -- ### the constants attached to the data
  set A' : Fin n → ℝ := fun j => (Work.CR.Flat.iterDerivNorm 0 (g j) Set.univ).toReal with hA'def
  set K' : Fin n → ℝ := fun j => (Work.CR.Flat.holderSeminorm 0 α (g j) Set.univ).toReal with hK'def
  have hA'0 : ∀ j, 0 ≤ A' j := fun j => ENNReal.toReal_nonneg
  have hK'0 : ∀ j, 0 ≤ K' j := fun j => ENNReal.toReal_nonneg
  have hA'lt : ∀ j, Work.CR.Flat.iterDerivNorm 0 (g j) Set.univ ≠ ⊤ := fun j =>
    lt_top_iff_ne_top.mp (lt_of_le_of_lt
      (Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α (g j) Set.univ (Nat.zero_le 0))
      ((hgfin j)))
  have hK'lt : ∀ j, Work.CR.Flat.holderSeminorm 0 α (g j) Set.univ ≠ ⊤ := fun j =>
    lt_top_iff_ne_top.mp (lt_of_le_of_lt
      (Work.CR.Flat.holderSeminorm_le_holderNorm 0 α (g j) Set.univ (Nat.zero_le 0))
      ((hgfin j)))
  have hA'eq : ∀ j, ENNReal.ofReal (A' j) = Work.CR.Flat.iterDerivNorm 0 (g j) Set.univ :=
    fun j => ENNReal.ofReal_toReal (hA'lt j)
  have hK'eq : ∀ j, ENNReal.ofReal (K' j) = Work.CR.Flat.holderSeminorm 0 α (g j) Set.univ :=
    fun j => ENNReal.ofReal_toReal (hK'lt j)
  have hgA : ∀ j x, ‖g j x‖ ≤ A' j := by
    intro j x
    have h1 : ENNReal.ofReal ‖g j x‖ ≤ Work.CR.Flat.iterDerivNorm 0 (g j) Set.univ := by
      rw [← norm_iteratedFDerivWithin_zero (𝕜 := ℝ) (f := g j) (s := Set.univ) (x := x)]
      exact Work.CR.Flat.le_iterDerivNorm 0 (g j) Set.univ (Set.mem_univ x)
    rw [← hA'eq j] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (hA'0 j)).mp h1
  have hgK : ∀ j x y, ‖g j x - g j y‖ ≤ K' j * ‖x - y‖ ^ α := by
    intro j x y
    rcases eq_or_ne x y with rfl | hxy
    · simp [Real.zero_rpow (ne_of_gt hα)]
    · have h1 : ENNReal.ofReal (‖g j x - g j y‖ / ‖x - y‖ ^ α)
          ≤ Work.CR.Flat.holderSeminorm 0 α (g j) Set.univ := by
        simpa [Work.NN.Core.norm_iteratedFDerivWithin_zero_sub (g j) Set.univ x y] using
          Work.CR.Flat.le_holderSeminorm 0 α (g j) Set.univ (Set.mem_univ x) (Set.mem_univ y) hxy
      rw [← hK'eq j] at h1
      have h2 : ‖g j x - g j y‖ / ‖x - y‖ ^ α ≤ K' j :=
        (ENNReal.ofReal_le_ofReal_iff (hK'0 j)).mp h1
      calc ‖g j x - g j y‖ = (‖g j x - g j y‖ / ‖x - y‖ ^ α) * ‖x - y‖ ^ α := by
            rw [div_mul_cancel₀]
            exact (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α).ne'
        _ ≤ K' j * ‖x - y‖ ^ α :=
            mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (norm_nonneg _) α)
  set S : ℝ := ∑ j, (A' j + K' j) with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => add_nonneg (hA'0 j) (hK'0 j)
  have h0j : ∀ j, Work.CR.Flat.holderNorm 0 α (g j) Set.univ = ENNReal.ofReal (A' j + K' j) := by
    intro j
    rw [Work.NN.Core.holderNorm_zero_eq, ← hA'eq j, ← hK'eq j,
      ENNReal.ofReal_add (hA'0 j) (hK'0 j)]
  have hA'leS : ∀ j, A' j ≤ S := by
    intro j
    calc A' j ≤ A' j + K' j := le_add_of_nonneg_right (hK'0 j)
      _ ≤ S := Finset.single_le_sum (f := fun j => A' j + K' j)
          (fun j _ => add_nonneg (hA'0 j) (hK'0 j)) (Finset.mem_univ j)
  have hAgS : ∀ j x, ‖g j x‖ ≤ S := fun j x => (hgA j x).trans (hA'leS j)
  have hsum_g : (∑ j, Work.CR.Flat.holderNorm 0 α (g j) Set.univ) = ENNReal.ofReal S :=
    (Finset.sum_congr rfl fun j _ => h0j j).trans (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => add_nonneg (hA'0 j) (hK'0 j)), ← hSdef])
  -- ### the smooth approximations
  have hst : ∀ j, r j / 2 < r j := fun j => by linarith [hr j]
  choose G hGsmooth hGbound hHolder hGsupp hGconv using fun j =>
    bmSmoothApprox (c := c) (s := fun j => r j / 2) (r := r) hα (hK'0 j) hst (hgA j) (hgK j)
      (hgsupp j)
  have hGsmooth1 : ∀ j m, ContDiff ℝ 1 (G j m) := fun j m => (hGsmooth j m).of_le (by norm_num)
  have hGgS : ∀ j m x, ‖G j m x‖ ≤ S := fun j m x => (hGbound j m x).trans (hA'leS j)
  -- ### the `C^{1,α}` bound for each approximation
  have hbound : ∀ m, Work.CR.Flat.holderNorm 1 α (bmPotential (fun j => G j m))
      (polydisc c (fun j => r j / 2)) ≤ ENNReal.ofReal (C₁ * S) := by
    intro m
    have hsupp2 : ∀ j z, (∃ k, (2 * r k) / 2 ≤ ‖z k - c k‖) → G j m z = 0 := by
      intro j z hz
      obtain ⟨k, hk⟩ := hz
      exact hGsupp j m z ⟨k, by rw [show 2 * r k / 2 = r k from by ring] at hk; exact hk⟩
    have hmain := hC₁ (fun j => G j m) (fun j => hGsmooth1 j m) hsupp2
    have hle_j : ∀ j, Work.CR.Flat.holderNorm 0 α (G j m) Set.univ
        ≤ ENNReal.ofReal (A' j + K' j) := by
      intro j
      have h1 : Work.CR.Flat.iterDerivNorm 0 (G j m) Set.univ ≤ ENNReal.ofReal (A' j) := by
        rw [Work.CR.Flat.iterDerivNorm_zero]
        exact iSup₂_le fun z _ => ENNReal.ofReal_le_ofReal (hGbound j m z)
      have h2 : Work.CR.Flat.holderSeminorm 0 α (G j m) Set.univ ≤ ENNReal.ofReal (K' j) := by
        rw [Work.CR.Flat.holderSeminorm]
        refine iSup₂_le fun x _ => iSup₂_le fun y _ => iSup_le fun hxy => ?_
        rw [Work.NN.Core.norm_iteratedFDerivWithin_zero_sub (G j m) Set.univ x y]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [div_le_iff₀ (Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) α)]
        exact hHolder j m x y
      calc Work.CR.Flat.holderNorm 0 α (G j m) Set.univ
          = Work.CR.Flat.iterDerivNorm 0 (G j m) Set.univ
            + Work.CR.Flat.holderSeminorm 0 α (G j m) Set.univ :=
            Work.NN.Core.holderNorm_zero_eq α (G j m) Set.univ
        _ ≤ ENNReal.ofReal (A' j) + ENNReal.ofReal (K' j) := add_le_add h1 h2
        _ = ENNReal.ofReal (A' j + K' j) :=
            (ENNReal.ofReal_add (hA'0 j) (hK'0 j)).symm
    have hsum_eq : (∑ j, ENNReal.ofReal (A' j + K' j)) = ENNReal.ofReal S := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => add_nonneg (hA'0 j) (hK'0 j)), ← hSdef]
    have hSbound : (∑ j, Work.CR.Flat.holderNorm 0 α (G j m) Set.univ) ≤ ENNReal.ofReal S :=
      (Finset.sum_le_sum fun j _ => hle_j j).trans (le_of_eq hsum_eq)
    have hPsub : polydisc c (fun j => r j / 2) ⊆ polydisc c r :=
      polydisc_mono fun j => by linarith [hr j]
    have hmono := Work.CR.Flat.holderNorm_mono_set (isOpen_polydisc c _) (isOpen_polydisc c _)
      hPsub 1 α (bmPotential (fun j => G j m))
    calc Work.CR.Flat.holderNorm 1 α (bmPotential (fun j => G j m))
          (polydisc c (fun j => r j / 2))
        ≤ Work.CR.Flat.holderNorm 1 α (bmPotential (fun j => G j m)) (polydisc c r) := hmono
      _ = Work.CR.Flat.holderNorm 1 α (bmPotential (fun j => G j m))
            (polydisc c (fun j => 2 * r j / 2)) := by
          congr 1
          funext j
          ring
      _ ≤ ENNReal.ofReal C₁ * ∑ j, Work.CR.Flat.holderNorm 0 α (G j m) Set.univ := hmain
      _ ≤ ENNReal.ofReal C₁ * ENNReal.ofReal S := mul_le_mul_right hSbound _
      _ = ENNReal.ofReal (C₁ * S) := (ENNReal.ofReal_mul hC₁pos.le).symm
  have hL5 : ∀ m, (∀ z ∈ polydisc c (fun j => r j / 2),
        ‖bmPotential (fun j => G j m) z‖ ≤ C₁ * S) ∧
      (∀ x ∈ polydisc c (fun j => r j / 2), ∀ y ∈ polydisc c (fun j => r j / 2),
        ‖bmPotential (fun j => G j m) x - bmPotential (fun j => G j m) y‖
          ≤ C₁ * S * ‖x - y‖ ^ α) ∧
      (∀ z ∈ polydisc c (fun j => r j / 2),
        ‖fderiv ℝ (bmPotential (fun j => G j m)) z‖ ≤ C₁ * S) ∧
      (∀ x ∈ polydisc c (fun j => r j / 2), ∀ y ∈ polydisc c (fun j => r j / 2),
        ‖fderiv ℝ (bmPotential (fun j => G j m)) x
          - fderiv ℝ (bmPotential (fun j => G j m)) y‖ ≤ C₁ * S * ‖x - y‖ ^ α) :=
    fun m => holderNorm_one_bounds (isOpen_polydisc c _) (mul_nonneg hC₁pos.le hS0) (hbound m)
  -- ### the limits
  have hU : ∀ z, Tendsto (fun m => bmPotential (fun j => G j m) z) atTop
      (nhds (bmPotential g z)) :=
    bmPotential_tendsto_of_tendsto hn hr hS0 (fun m j => (hGsmooth j m).continuous)
      (fun j => continuous_of_holder_bound hα (hK'0 j) (hgK j))
      (fun m j z => hGgS j m z) (fun j z => hAgS j z) (fun m j z hz => hGsupp j m z hz)
      (fun j z hz => hgsupp j z (by obtain ⟨i, hi⟩ := hz; exact ⟨i, by linarith [hr i]⟩))
      (fun j z => hGconv j z)
  have hfsmooth : ∀ m (z : Fin n → ℂ), z ∈ polydisc c (fun j => r j / 2) →
      fderiv ℝ (bmPotential (fun j => G j m)) z = bmDerivData Rb cc (fun j => G j m) z := by
    intro m z hz
    have hbm : bmPotential (fun j => G j m) = fun w => bmPot (fun j => G j m) w :=
      funext fun w => bmPotential_eq_bmPot _ w
    rw [hbm]
    refine fderiv_bmPot_eq_bmDerivData hn hcc (fun j => hGsmooth1 j m) hRbpos
      (fun k x hx => ?_) (fun k x hx => ?_)
    · rw [hRbdef] at hx
      refine hGsupp k m x (exists_coord_le_of_le_norm hr ?_)
      calc (∑ j, r j) + ‖c‖ + 1 = 1 * ((∑ j, r j) + ‖c‖ + 1) := by ring
        _ ≤ 2 * Real.sqrt n * ((∑ j, r j) + ‖c‖ + 1) := by
            refine mul_le_mul_of_nonneg_right ?_ ?_
            · have h1 : (1 : ℝ) ≤ Real.sqrt n :=
                Real.one_le_sqrt.mpr (by exact_mod_cast Nat.succ_le_iff.mpr hn)
              linarith
            · have h1 : 0 < ∑ j, r j :=
                Finset.sum_pos (fun j _ => hr j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
              have h2 : 0 ≤ ‖c‖ := norm_nonneg c
              linarith
        _ ≤ ‖x‖ := hx
    · rw [hRbdef] at hx
      exact hGsupp k m (z + x) (shift_exists_coord_le hn hr hz hx)
  have hDeriv : ∀ z ∈ polydisc c (fun j => r j / 2), ∀ v : Fin n → ℂ,
      Tendsto (fun m => fderiv ℝ (bmPotential (fun j => G j m)) z v) atTop
        (nhds (bmDerivData Rb cc g z v)) := by
    intro z hz v
    have hconv' := tendsto_bmDerivData_apply hn hRbpos cc hα hK'0
      (fun m j x y => hHolder j m x y) hgK hGconv z v
    refine hconv'.congr' (Filter.Eventually.of_forall fun m => ?_)
    exact congrArg (fun L => L v) (hfsmooth m z hz).symm
  have hTay : ∀ᶠ m in atTop, ∀ z ∈ polydisc c (fun j => r j / 2), ∀ h,
      z + h ∈ polydisc c (fun j => r j / 2) →
      ‖bmPotential (fun j => G j m) (z + h) - bmPotential (fun j => G j m) z
        - fderiv ℝ (bmPotential (fun j => G j m)) z h‖ ≤ C₁ * S * ‖h‖ ^ (1 + α) := by
    filter_upwards with m
    intro z hz h hzh
    have hdiff : ∀ x, DifferentiableAt ℝ (bmPotential (fun j => G j m)) x := fun x =>
      ((bmPotential_contDiff_one (c := c) (r := fun j => 2 * r j) hn
        (fun j => by linarith [hr j]) (fun j => hGsmooth1 j m)
        (fun j z hz' => by
          obtain ⟨k, hk⟩ := hz'
          exact hGsupp j m z ⟨k, by rw [show 2 * r k / 2 = r k from by ring] at hk; exact hk⟩)
        ).differentiable (by norm_num)).differentiableAt
    have hres := holder_fderiv_taylor' hα (mul_nonneg hC₁pos.le hS0) hdiff (convex_polydisc c _)
      (fun x hx y hy => (hL5 m).2.2.2 x hx y hy) hz hzh
    simpa using hres
  have hHasFDeriv : ∀ z ∈ polydisc c (fun j => r j / 2),
      HasFDerivAt (bmPotential g) (bmDerivData Rb cc g z) z := by
    intro z hz
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    refine Asymptotics.IsLittleO.of_bound fun ε hε => ?_
    have hseg : ∀ᶠ h in nhds (0 : Fin n → ℂ), z + h ∈ polydisc c (fun j => r j / 2) := by
      have hmem : polydisc c (fun j => r j / 2) ∈ nhds z :=
        (isOpen_polydisc c (fun j => r j / 2)).mem_nhds hz
      have hz' : Tendsto (fun h : Fin n → ℂ => z + h) (nhds 0) (nhds z) := by
        simpa using (tendsto_const_nhds.add
          (tendsto_id : Tendsto (fun h : Fin n → ℂ => h) (nhds 0) (nhds 0)))
      exact hz'.eventually hmem
    have hcont : Tendsto (fun h : Fin n → ℂ => C₁ * S * ‖h‖ ^ α) (nhds 0) (nhds 0) := by
      have h1 : Tendsto (fun h : Fin n → ℂ => ‖h‖) (nhds 0) (nhds 0) := by
        simpa using (continuous_norm.tendsto (0 : Fin n → ℂ))
      have h2 : Tendsto (fun h : Fin n → ℂ => ‖h‖ ^ α) (nhds 0) (nhds (0 ^ α)) :=
        (Real.continuousAt_rpow_const 0 α (Or.inr hα.le)).tendsto.comp h1
      rw [Real.zero_rpow (ne_of_gt hα)] at h2
      simpa using h2.const_mul (C₁ * S)
    have hev : ∀ᶠ h in nhds (0 : Fin n → ℂ), C₁ * S * ‖h‖ ^ α < ε :=
      (tendsto_order.1 hcont).2 ε hε
    filter_upwards [hseg, hev] with h hzh hlt
    have hlim : Tendsto (fun m => bmPotential (fun j => G j m) (z + h)
        - bmPotential (fun j => G j m) z - fderiv ℝ (bmPotential (fun j => G j m)) z h)
        atTop (nhds (bmPotential g (z + h) - bmPotential g z - bmDerivData Rb cc g z h)) :=
      ((hU (z + h)).sub (hU z)).sub (hDeriv z hz h)
    have hbl := le_of_tendsto hlim.norm (hTay.mono fun m hm => hm z hz h hzh)
    calc ‖bmPotential g (z + h) - bmPotential g z - bmDerivData Rb cc g z h‖
        ≤ C₁ * S * ‖h‖ ^ (1 + α) := hbl
      _ = (C₁ * S * ‖h‖ ^ α) * ‖h‖ := by rw [rpow_one_add_mul hα (norm_nonneg h)]; ring
      _ ≤ ε * ‖h‖ := mul_le_mul_of_nonneg_right hlt.le (norm_nonneg h)
  intro z hz
  exact (hHasFDeriv z hz).differentiableAt

end Work.NN.Core
