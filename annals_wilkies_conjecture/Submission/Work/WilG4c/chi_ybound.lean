/-
  WilG4c — the `y`-bound for `ψ ∘ χ` needed by `hbdd_sup_finite` (BNZ §5.4).

  `chi g L' m` is the "junk extension" of the `L'`-th directional derivative of `g` over the
  `C^m`-locus of `g` (equal to `iterDir L' g` on the locus, `0` off it).  The lemma below bounds
  the `y`-partials of `ψ ∘ chi g L' m` on the interior of its `C^1`-locus, off a finite set of
  `x`, by the `y`-bounds for `iterDir (i.succ :: L') g` supplied by the induction hypothesis
  (`hIH`).

  The argument.  Fix `x` avoiding the finite exceptional set and one `y`-direction `i`.  On the
  open set where `g` is `C^m`, `ψ ∘ chi` agrees with `ψ ∘ iterDir L' g`, so the chain rule gives
  the `y`-derivative `ψ'(∂^{L'}g) · ∂^{i.succ::L'}g`, bounded by `(1/2)·C` where `C` bounds
  `∂^{i.succ::L'}g` on the slice (`dpsi ≤ 1/2`, `dpsi > 0`).  On the rest of the `C^1`-locus of
  `ψ ∘ chi` (where `g` fails to be `C^m` in a whole neighbourhood — the locus of `ContDiffAt` is
  open) the function `ψ ∘ chi` is constant equal to `ψ 0 = 1/2` along the slice.  Points on the
  boundary of the `C^m`-locus are handled by *continuity of `fderiv` along the slice*: they are
  limits of good points, on which the bound holds, or the function is locally constant.

  The key point that makes the argument go through on a single slice is that the bound `C` is
  slice-wise: approximating along the curve `t ↦ pt x (y + t·eᵢ)` keeps the first coordinate `x`
  fixed.
-/
import Mathlib
import Submission.Work.WilG4c.hbdd_defs
import Submission.Work.WilG4c.IterDirAux

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilG4c

open WilkiesDesign

/-! ## Elementary facts about `psi` and its derivative -/

theorem chiY_dpsi_pos (u : ℝ) : 0 < Work.WilkG4c.dpsi u := by
  rw [Work.WilkG4c.dpsi]
  positivity

theorem chiY_psi_zero : Work.WilkG4c.psi 0 = 1 / 2 := by
  rw [Work.WilkG4c.psi]
  norm_num

theorem chiY_fderiv_psi (hpsi : ∀ u : ℝ, HasDerivAt Work.WilkG4c.psi (Work.WilkG4c.dpsi u) u)
    (u w : ℝ) : (fderiv ℝ Work.WilkG4c.psi u) w = Work.WilkG4c.dpsi u * w := by
  rw [(hpsi u).hasFDerivAt.fderiv]
  simp [smul_eq_mul, mul_comm]

/-- The affine curve `t ↦ pt x y + t • e` in coordinates: it is the slice `y + t • eᵢ`. -/
theorem chiY_pt_add_smul {n : ℕ} (x : ℝ) (y : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    Work.WilkG4c.pt x y + t • (Pi.single i.succ (1 : ℝ)) =
      Work.WilkG4c.pt x (y + t • Pi.single i (1 : ℝ)) := by
  funext j
  induction j using Fin.cases with
  | zero => simp [Work.WilkG4c.pt_zero]
  | succ k => simp [Work.WilkG4c.pt_succ, Pi.single_apply, Fin.succ_inj]

/-! ## The chain rule on the `C^m`-locus -/

/-- On the `C^m`-locus of `g`, the `j`-th partial derivative of `ψ ∘ chi g L' m` is
`ψ'(∂^{L'}g) · ∂^{j::L'}g`. -/
theorem chiY_fderiv_good {n : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ} (L' : List (Fin (n + 1))) {m : ℕ}
    (hm : L'.length + 1 = m)
    (hpsi : ∀ u : ℝ, HasDerivAt Work.WilkG4c.psi (Work.WilkG4c.dpsi u) u)
    {v : Fin (n + 1) → ℝ} (hv : ContDiffAt ℝ m g v) (j : Fin (n + 1)) :
    (fderiv ℝ (fun u => Work.WilkG4c.psi (Work.WilkG4c.chi g L' m u)) v) (Pi.single j 1)
      = Work.WilkG4c.dpsi (Work.WilkG4c.iterDir L' g v) * Work.WilkG4c.iterDir (j :: L') g v := by
  classical
  have hev : (fun u => Work.WilkG4c.psi (Work.WilkG4c.chi g L' m u)) =ᶠ[𝓝 v]
      (fun u => Work.WilkG4c.psi (Work.WilkG4c.iterDir L' g u)) := by
    filter_upwards [hv.eventually (by simp)] with u hu
    rw [Work.WilkG4c.chi_of_contDiffAt g L' m hu]
  have hditer : DifferentiableAt ℝ (Work.WilkG4c.iterDir L' g) v := by
    have hg : ContDiffAt ℝ (L'.length + 1) g v := by
      convert hv using 2
      exact_mod_cast hm
    exact (iterDir_contDiffAt g L' 1 v hg).differentiableAt_one
  rw [hev.fderiv_eq]
  change (fderiv ℝ (Work.WilkG4c.psi ∘ (Work.WilkG4c.iterDir L' g)) v) (Pi.single j 1) = _
  rw [fderiv_comp v (hpsi _).differentiableAt hditer, ContinuousLinearMap.comp_apply,
    chiY_fderiv_psi hpsi]
  congr 1

/-! ## The slice bound -/

/-- The main estimate: on a slice `{pt x ·}` on which `C` bounds `∂^{i.succ :: L'}g` over the
`C^m`-locus, the `y`-partial of `ψ ∘ chi g L' m` is bounded by `C / 2` on the interior of the
`C^1`-locus of `ψ ∘ chi g L' m`. -/
theorem chiY_slice_bound {n : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ} (L' : List (Fin (n + 1))) {m : ℕ}
    (hm : L'.length + 1 = m)
    (hpsi : ∀ u : ℝ, HasDerivAt Work.WilkG4c.psi (Work.WilkG4c.dpsi u) u)
    (hpsi_le : ∀ u : ℝ, Work.WilkG4c.dpsi u ≤ 1 / 2)
    {x : ℝ} {y : Fin n → ℝ} (hy : y ∈ openCube n) (i : Fin n) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ y' ∈ openCube n, ContDiffAt ℝ m g (Work.WilkG4c.pt x y') →
      |Work.WilkG4c.iterDir (i.succ :: L') g (Work.WilkG4c.pt x y')| ≤ C)
    (hz : Work.WilkG4c.pt x y ∈ interior {z | ContDiffAt ℝ 1
        (fun v => Work.WilkG4c.psi (Work.WilkG4c.chi g L' m v)) z}) :
    |(fderiv ℝ (fun v => Work.WilkG4c.psi (Work.WilkG4c.chi g L' m v))
        (Work.WilkG4c.pt x y)) (Pi.single i.succ 1)| ≤ 1 / 2 * C := by
  classical
  set F : (Fin (n + 1) → ℝ) → ℝ := fun v => Work.WilkG4c.psi (Work.WilkG4c.chi g L' m v) with hF
  have hcF : ContDiffAt ℝ 1 F (Work.WilkG4c.pt x y) := by
    rw [hF]; exact interior_subset hz
  set e : Fin (n + 1) → ℝ := Pi.single i.succ 1 with he
  set γ : ℝ → Fin (n + 1) → ℝ := fun t => Work.WilkG4c.pt x y + t • e with hγ
  have hγ0 : γ 0 = Work.WilkG4c.pt x y := by simp [hγ]
  have hpt : ∀ t : ℝ, γ t = Work.WilkG4c.pt x (y + t • Pi.single i (1 : ℝ)) := by
    intro t
    rw [hγ, he]
    exact chiY_pt_add_smul x y i t
  have hγderiv : HasDerivAt γ e 0 := by
    have h1 : HasDerivAt (fun t : ℝ => t • e) e 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const e
    have h2 := h1.const_add (Work.WilkG4c.pt x y)
    simpa [hγ] using h2
  have hγcont : ContinuousAt γ 0 := hγderiv.continuousAt
  have hfdcont : ContinuousAt (fderiv ℝ F) (γ 0) := by
    rw [hγ0]
    exact hcF.continuousAt_fderiv (by simp)
  have hφcont : ContinuousAt (fun t : ℝ => (fderiv ℝ F (γ t)) e) 0 :=
    (hfdcont.comp hγcont).clm_apply continuousAt_const
  -- the sliced cube is a neighbourhood
  have hy_nhds : openCube n ∈ 𝓝 y := by
    have hpi : openCube n = Set.pi Set.univ (fun _ : Fin n => Set.Ioo (0 : ℝ) 1) := by
      ext t; simp [openCube]
    rw [hpi]
    exact (isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)).mem_nhds (fun i _ => hy i)
  have hcube_ev : ∀ᶠ t in 𝓝 (0 : ℝ),
      (y + t • Pi.single i (1 : ℝ)) ∈ openCube n := by
    let c : Fin n → ℝ := Pi.single i 1
    have h1 : HasDerivAt (fun t : ℝ => y + t • c) c 0 := by
      have h2 := (hasDerivAt_id (0 : ℝ)).smul_const c
      simpa using h2.const_add y
    have hcurve0 : (fun t : ℝ => y + t • c) 0 = y := by simp
    have htend : Filter.Tendsto (fun t : ℝ => y + t • c) (𝓝 0) (𝓝 y) := by
      simpa using h1.continuousAt.tendsto
    exact htend.eventually hy_nhds
  -- the good points satisfy the bound
  have hS_bound : ∀ᶠ t in 𝓝 (0 : ℝ),
      (ContDiffAt ℝ m g (γ t) → |(fderiv ℝ F (γ t)) e| ≤ 1 / 2 * C) := by
    filter_upwards [hcube_ev] with t hcube
    intro ht
    have hFeq : (fderiv ℝ F (γ t)) e
        = Work.WilkG4c.dpsi (Work.WilkG4c.iterDir L' g (γ t))
            * Work.WilkG4c.iterDir (i.succ :: L') g (γ t) := by
      rw [hF, he]
      exact chiY_fderiv_good L' hm hpsi ht i.succ
    have hiter : |Work.WilkG4c.iterDir (i.succ :: L') g (γ t)| ≤ C := by
      have h1 := hC (y + t • Pi.single i (1 : ℝ)) hcube (by rw [← hpt t]; exact ht)
      simpa [hpt t] using h1
    have hd : |Work.WilkG4c.dpsi (Work.WilkG4c.iterDir L' g (γ t))| ≤ 1 / 2 := by
      rw [abs_of_pos (chiY_dpsi_pos _)]
      exact hpsi_le _
    rw [hFeq, abs_mul]
    exact mul_le_mul hd hiter (abs_nonneg _) (by norm_num)
  by_cases hfreq : ∃ᶠ t in 𝓝 (0 : ℝ), ContDiffAt ℝ m g (γ t)
  · have hfr : ∃ᶠ t in 𝓝 (0 : ℝ), |(fderiv ℝ F (γ t)) e| ≤ 1 / 2 * C :=
      (hfreq.and_eventually hS_bound).mono (fun t ht => ht.2 ht.1)
    have htend : Filter.Tendsto (fun t : ℝ => |(fderiv ℝ F (γ t)) e|) (𝓝 0)
        (𝓝 |(fderiv ℝ F (γ 0)) e|) := by
      have h := hφcont.norm.tendsto
      simpa [Real.norm_eq_abs] using h
    have h2 : |(fderiv ℝ F (γ 0)) e| ≤ 1 / 2 * C := by
      by_contra hcon
      rw [not_le] at hcon
      have hcont2 : ContinuousAt (fun t : ℝ => |(fderiv ℝ F (γ t)) e|) 0 := hφcont.norm
      have hmem : {s : ℝ | 1 / 2 * C < |(fderiv ℝ F (γ s)) e|} ∈ 𝓝 (0 : ℝ) :=
        hcont2.preimage_mem_nhds (isOpen_Ioi.mem_nhds hcon)
      exact hfr (Filter.Eventually.mono hmem (fun t ht => not_le.mpr ht))
    rw [hγ0] at h2
    simpa [hF, he] using h2
  · have hnot : ∀ᶠ t in 𝓝 (0 : ℝ), ¬ ContDiffAt ℝ m g (γ t) := by
      by_contra hc
      exact hfreq hc
    have hconst : (fun t : ℝ => F (γ t)) =ᶠ[𝓝 (0 : ℝ)] (fun _ => 1 / 2) := by
      filter_upwards [hnot] with t ht
      rw [hF]
      change Work.WilkG4c.psi (Work.WilkG4c.chi g L' m (γ t)) = 1 / 2
      rw [Work.WilkG4c.chi_of_not_contDiffAt g L' m ht, chiY_psi_zero]
    have hFdiff : HasFDerivAt F (fderiv ℝ F (γ 0)) (γ 0) := by
      rw [hγ0]
      exact hcF.differentiableAt_one.hasFDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => F (γ t)) ((fderiv ℝ F (γ 0)) e) 0 :=
      hFdiff.comp_hasDerivAt 0 hγderiv
    have hder : deriv (fun t : ℝ => F (γ t)) 0 = 0 := by
      rw [hconst.deriv_eq]
      simp
    have hc : (fderiv ℝ F (γ 0)) e = 0 := by
      rw [← hcomp.deriv, hder]
    have hz0 : (fderiv ℝ F (Work.WilkG4c.pt x y)) (Pi.single i.succ 1) = 0 := by
      rw [← he, ← hγ0]
      exact hc
    rw [hz0, abs_zero]
    exact mul_nonneg (by norm_num) hC0

/-! ## The lemma -/

theorem chi_ybound {n : ℕ} {g : (Fin (n + 1) → ℝ) → ℝ} (L' : List (Fin (n + 1))) {m : ℕ}
    (hm : L'.length + 1 = m)
    (hpsi : ∀ u : ℝ, HasDerivAt Work.WilkG4c.psi (Work.WilkG4c.dpsi u) u)
    (hpsi_le : ∀ u : ℝ, Work.WilkG4c.dpsi u ≤ 1 / 2)
    (hIH : ∀ i : Fin n, ∃ s : Finset ℝ, ∀ x ∈ Work.WilkG4c.I, x ∉ (s : Set ℝ) →
      BddAbove ((fun y => |Work.WilkG4c.iterDir (i.succ :: L') g (Work.WilkG4c.pt x y)|) ''
        {y : Fin n → ℝ | y ∈ WilkiesDesign.openCube n ∧
          ContDiffAt ℝ m g (Work.WilkG4c.pt x y)})) :
    ∃ s : Finset ℝ, ∀ x ∈ Work.WilkG4c.I, x ∉ (s : Set ℝ) → ∃ B : ℝ, ∀ y ∈ WilkiesDesign.openCube n,
      Work.WilkG4c.pt x y ∈ interior {z | ContDiffAt ℝ 1
        (fun v => Work.WilkG4c.psi (Work.WilkG4c.chi g L' m v)) z} →
      ∀ i : Fin n, |(fderiv ℝ (fun v => Work.WilkG4c.psi (Work.WilkG4c.chi g L' m v))
        (Work.WilkG4c.pt x y)) (Pi.single i.succ 1)| ≤ B := by
  classical
  choose S hS using hIH
  refine ⟨Finset.univ.biUnion S, ?_⟩
  intro x hxI hxnot
  have hxS : ∀ i : Fin n, x ∉ (S i : Set ℝ) := by
    intro i hi
    exact hxnot (by
      rw [Finset.mem_coe, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ i, Finset.mem_coe.mp hi⟩)
  choose b hb using fun i : Fin n => hS i x hxI (hxS i)
  refine ⟨∑ i : Fin n, max (b i) 0, ?_⟩
  intro y hy hz i
  have hC0 : (0 : ℝ) ≤ max (b i) 0 := le_max_right _ _
  have hC : ∀ y' ∈ openCube n, ContDiffAt ℝ m g (Work.WilkG4c.pt x y') →
      |Work.WilkG4c.iterDir (i.succ :: L') g (Work.WilkG4c.pt x y')| ≤ max (b i) 0 := by
    intro y' hy' hcd
    exact le_trans (hb i ⟨y', ⟨hy', hcd⟩, rfl⟩) (le_max_left _ _)
  have h1 := chiY_slice_bound (x := x) L' hm hpsi hpsi_le hy i hC0 hC hz
  refine le_trans h1 ?_
  calc (1 / 2 : ℝ) * max (b i) 0 ≤ 1 * max (b i) 0 :=
        mul_le_mul_of_nonneg_right (by norm_num) hC0
    _ = max (b i) 0 := one_mul _
    _ ≤ ∑ j : Fin n, max (b j) 0 :=
        Finset.single_le_sum (fun j _ => le_max_right _ _) (Finset.mem_univ i)

end Work.WilG4c
