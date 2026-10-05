import Mathlib
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.Nodes
import Submission.Work.RPB1a.curveIsotopy_of_loopFamily
import Submission.Work.RPB1a.loopFamily_concat3
import Submission.Work.RPB1a.loopFamily_affine
import Submission.Work.RPB1a.loopFamily_reverse
import Submission.Work.RPB1a.loopFamily_comp_pm
import Submission.Work.RPB1a.isSmoothLoop_of_loopFamily
import Submission.Work.RPB1a.isSmoothLoop_of_isSmoothJordan
import Submission.Work.RPB1a.isSmoothLoop_comp_neg
import Submission.Work.RPB1a.isSmoothLoop_circle_trace
import Submission.Work.RPB1a.exists_trigPoly_C1_approx
import Submission.Work.RPB1a.straightLine_loopFamily
import Submission.Work.RPB1a.laurentPoly_exp
import Submission.Work.RPB1a.laurentPoly_differentiableOn
import Submission.Work.RPB1a.laurent_collar
import Submission.Work.RPB1a.reparam_loopFamily
import Submission.Work.RPB1a.inv_image_annulus_inter_ball
import Submission.Work.RPB1a.inv_image_annulus_diff_closedBall
import Submission.Work.RPB1a.flip_collar_data
import Submission.Work.RPB1a.isOpen_image_of_differentiableOn_of_injOn
import Submission.Work.RPB1a.isOpen_annulus
import Submission.Work.RPB1a.contDiff_trigPoly
import Submission.Work.RPB1a.trigPoly_periodic
import Submission.Work.RPB1a.range_comp_neg
import Submission.Work.RPB.B1a.RiemannMapNodeSmooth

namespace Work.RPB.B1chain

open Complex Set Metric
open scoped ContDiff Real
open Work.RPB1a

/-- **The tail of the geometric chain (steps 5–9), smooth-boundary form.**

This is `Work.RPB1a.chain_tail` with the Riemann-map node `hN6` replaced by
`Work.RPB.B1a.RiemannMapNodeSmooth`, which is the form the in-house proof
(`Work.RPB.B1a.riemannMapNodeSmooth`) discharges: it takes the smooth bounding loop and
`frontier D = Set.range v` among its hypotheses, instead of only `IsJordanCurveSet (frontier D)`.
Consequently `hN5` is not needed here — the primitives hypothesis is already discharged inside the
node.  Everything else is verbatim. -/
private theorem chain_tail
    {u : ℝ → ℂ}
    {L : ℝ → ℝ → ℂ} (hL : IsLoopFamily L) (hL0 : ∀ t, L 0 t = u t)
    (v : ℝ → ℂ) (hv : IsSmoothLoop v)
    (D : Set ℂ) (hDo : IsOpen D) (hDc : IsConnected D) (hDb : Bornology.IsBounded D)
    (hDcc : IsConnected Dᶜ) (hJ : IsJordanCurveSet (frontier D))
    (hDfr : frontier D = range v) (hDdisj : Disjoint D (range v))
    (hDext : range v ⊆ closure (D ∪ range v)ᶜ)
    (Γ : ℂ → ℂ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hΓd : DifferentiableOn ℂ Γ (annulus ρ)) (hΓi : InjOn Γ (annulus ρ))
    (hΓ' : ∀ w ∈ annulus ρ, deriv Γ w ≠ 0)
    (hΓcirc : ∀ t : ℝ, Γ (Complex.exp (t * I)) = v t)
    (hin : Γ '' (annulus ρ ∩ ball 0 1) ⊆ D)
    (hout : Disjoint (Γ '' (annulus ρ \ closedBall 0 1)) D)
    (δ : ℝ) (hδ : δ = 1 ∨ δ = -1) (hδv : ∀ t, v t = L 1 (δ * t))
    (hN6 : Work.RPB.B1a.RiemannMapNodeSmooth) (hN7 : ReflectionNode) (hN8 : LevelCirclesNode) :
    ∃ (a₀ : ℝ) (F0 : ℂ) (e : ℝ), 0 < a₀ ∧ (e = 1 ∨ e = -1) ∧
      ∃ c : ℝ → ℝ → ℂ, IsLoopFamily c ∧ (∀ t : ℝ, c 0 t = Complex.exp (t * I)) ∧
        ∀ t : ℝ, c 1 t = (u (e * t) - F0) / (a₀ : ℂ) := by
  -- Step 5: the Riemann map (the smooth-boundary form of node N6)
  obtain ⟨Φ, hΦc, hΦd, hΦi, hΦim, hΦs, a, ha, hΦa⟩ :=
    hN6 v hv D hDo hDc hDb hDcc hDfr
  have hΦs0 : MapsTo Φ (sphere (0 : ℂ) 1) (frontier D) := by
    rw [hDfr]; exact hΦs
  -- Step 6: reflection across the analytic boundary
  obtain ⟨R, hR, F, hFd, hFi, hF', hEqFΦ, σ, hσ, hFσ⟩ :=
    hN7 v hv D hDo hDfr hDdisj Γ ρ hρ0 hρ1 hΓd hΓi hΓ' hΓcirc hin hout
      Φ hΦc hΦd hΦi hΦim hΦs
  have hF0a : deriv F 0 = a := by
    have hmem : closedBall (0 : ℂ) 1 ∈ nhds (0 : ℂ) := Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num)
    have hev : F =ᶠ[nhds (0 : ℂ)] Φ := Filter.eventually_of_mem hmem (fun z hz => hEqFΦ hz)
    exact hev.deriv_eq.trans hΦa
  have hvs : IsSmoothLoop (fun t => v (σ t)) := by
    have h := isSmoothLoop_circle_trace F R hR hFd hFi hF'
    have hfun : (fun t : ℝ => F (Complex.exp (t * I))) = (fun t : ℝ => v (σ t)) := funext hFσ
    rwa [hfun] at h
  -- Step 7: the level-circle family
  obtain ⟨c₁, hc₁, hc₁0, hc₁1⟩ := hN8 F R hR hFd hFi hF' a ha hF0a
  -- Step 8: the free reparametrisation
  obtain ⟨e_re, he_re, c_rep, hc_rep, hc_rep0, hc_rep1⟩ := reparam_loopFamily v hv σ hσ hvs
  -- the affine normalisation `T`
  let T : ℂ → ℂ := fun z => (z - F 0) / (a : ℂ)
  have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  have hTcomp : ∀ {c : ℝ → ℝ → ℂ}, IsLoopFamily c → IsLoopFamily (fun s t => T (c s t)) := by
    intro c hc
    have h := loopFamily_affine hc ((a : ℂ)⁻¹) (-((a : ℂ)⁻¹ * F 0)) (inv_ne_zero haC)
    have hfun : (fun s t => T (c s t)) =
        (fun s t => (a : ℂ)⁻¹ * c s t + -((a : ℂ)⁻¹ * F 0)) := by
      funext s t
      show (c s t - F 0) / (a : ℂ) = (a : ℂ)⁻¹ * c s t + -((a : ℂ)⁻¹ * F 0)
      rw [div_eq_mul_inv]
      ring
    rwa [hfun]
  let cmid : ℝ → ℝ → ℂ := fun s t => T (c_rep s t)
  have hcmid : IsLoopFamily cmid := hTcomp hc_rep
  have hefin : δ * e_re = 1 ∨ δ * e_re = -1 := by
    rcases hδ with h | h <;> rcases he_re with h2 | h2 <;> (rw [h, h2]; norm_num)
  let clast : ℝ → ℝ → ℂ := fun s t => T (L (1 - s) ((δ * e_re) * t))
  have hclast : IsLoopFamily clast := by
    show IsLoopFamily (fun s t => T (L (1 - s) ((δ * e_re) * t)))
    have hLrev : IsLoopFamily (fun s t => L (1 - s) t) := loopFamily_reverse hL
    exact hTcomp (loopFamily_comp_pm hLrev hefin)
  -- Step 9: the three pieces match end to start
  have hclast0 : ∀ t, T (L (1 - 0) ((δ * e_re) * t)) = T (v (e_re * t)) := by
    intro t
    apply congrArg T
    rw [show (1 : ℝ) - 0 = 1 by norm_num]
    rw [show (δ * e_re) * t = δ * (e_re * t) by ring]
    exact (hδv (e_re * t)).symm
  have hclast1 : ∀ t, T (L (1 - 1) ((δ * e_re) * t)) = T (u ((δ * e_re) * t)) := by
    intro t
    apply congrArg T
    rw [show (1 : ℝ) - 1 = 0 by norm_num]
    exact hL0 _
  have h12 : ∀ t, c₁ 1 t = cmid 0 t := by
    intro t
    show c₁ 1 t = T (c_rep 0 t)
    rw [hc₁1 t, hc_rep0 t, ← hFσ t]
  have h23 : ∀ t, cmid 1 t = clast 0 t := by
    intro t
    show T (c_rep 1 t) = T (L (1 - 0) ((δ * e_re) * t))
    rw [hc_rep1 t]
    exact (hclast0 t).symm
  obtain ⟨H, hH, hH0, hH1⟩ := loopFamily_concat3 c₁ cmid clast hc₁ hcmid hclast h12 h23
  refine ⟨a, F 0, δ * e_re, ha, hefin, H, hH, ?_, ?_⟩
  · intro t
    rw [hH0 t, hc₁0 t]
  · intro t
    rw [hH1 t]
    show T (L (1 - 1) ((δ * e_re) * t)) = (u ((δ * e_re) * t) - F 0) / (a : ℂ)
    rw [hclast1 t]

/-- N10's geometric chain, smooth-boundary form: the library-facing nodes produce a loop family from
the unit circle to `(γ (e^{it}) - F0)/a₀`, with `a₀ > 0` real, `F0 : ℂ` and `e = ±1`.

This is `Work.RPB1a.loopFamily_chain_of_nodes` with the Riemann-map node `hN6` replaced by
`Work.RPB.B1a.RiemannMapNodeSmooth` (`hN5` is dropped: the primitives hypothesis is discharged
inside that node).  The numbered steps below are those of the original.

1. `u := γ ∘ Circle.exp` is a smooth loop (`isSmoothLoop_of_isSmoothJordan`).
2. `straightLine_loopFamily u hu` gives `ε > 0`; `exists_trigPoly_C1_approx u hu.1 hu.2.1 ε hε` gives
   `N, a` with `‖v₀ - u‖ < ε` and `‖v₀' - u'‖ < ε`, where `v₀ := trigPoly N a`
   (`contDiff_trigPoly`, `trigPoly_periodic`); the straight-line family `L s t = u t + s*(v₀ t - u t)`
   is an `IsLoopFamily`, hence `v₀` is a smooth loop (`isSmoothLoop_of_loopFamily`, `s = 1`).
3. `laurent_collar N a hv₀` gives `ρ`; `Γ := laurentPoly N a` has `Γ (e^{it}) = v₀ t`
   (`laurentPoly_exp`), is holomorphic on `annulus ρ` (`laurentPoly_differentiableOn`, since
   `annulus ρ ⊆ {0}ᶜ`), injective, with `deriv Γ ≠ 0`; its image is open
   (`isOpen_image_of_differentiableOn_of_injOn` with `isOpen_annulus`).
4. `jordan_domain_of_loop v₀ hv₀` gives `D`, and `collar_side` tells which half of the collar lies in
   `D`.  In the outer case (`Γ '' (annulus ρ \ closedBall 0 1) ⊆ D`) replace `Γ` by
   `Γ̃ w = Γ w⁻¹` and `v₀` by `v t = v₀ (-t)`: the collar data transport is
   `flip_collar_data`, the side identities are `inv_image_annulus`,
   `inv_image_annulus_inter_ball`, `inv_image_annulus_diff_closedBall`, `v` is a smooth loop by
   `isSmoothLoop_comp_neg` and `range v = range v₀` by `range_comp_neg`.
5. the smooth-boundary Riemann-map node gives `Φ` and `a₀ > 0` with `deriv Φ 0 = a₀`.
6. `analytic_extension_of_collar` gives `F`, `R > 1` and `σ` with `F (e^{it}) = v (σ t)`;
   `IsSmoothLoop (v ∘ σ)` is `isSmoothLoop_circle_trace` transported along that identity, and
   `deriv F 0 = a₀` follows from `EqOn F Φ (closedBall 0 1)`.
7. `discLoopFamily F R ... a₀ ...` gives the level-circle family `c₁`.
8. `reparam_loopFamily v hv σ hσ (v ∘ σ)` gives `e = ±1` and a family from `v ∘ σ` to `v (e .)`;
   put `T z := (z - F 0)/a₀`.
9. `loopFamily_concat3` glues `c₁`, `T ∘ c_rep` and `T ∘ (L (1-s) (e* t))`, where `e* = e` in the
   inner case and `e* = -e` in the outer case (`loopFamily_affine` for `T`, whose multiplier
   `(a₀:ℂ)⁻¹` is nonzero, `loopFamily_reverse`, `loopFamily_comp_pm`), giving the required family. -/
theorem loopFamily_chain_of_nodes
    (hN4 : JordanDomainNode) (hN4b : CollarSideNode)
    (hN6 : Work.RPB.B1a.RiemannMapNodeSmooth) (hN7 : ReflectionNode) (hN8 : LevelCirclesNode) :
    ∀ γ : Circle → ℂ, Work.RPV.IsSmoothJordan γ →
      ∃ (a₀ : ℝ) (F0 : ℂ) (e : ℝ), 0 < a₀ ∧ (e = 1 ∨ e = -1) ∧
        ∃ c : ℝ → ℝ → ℂ, IsLoopFamily c ∧ (∀ t : ℝ, c 0 t = Complex.exp (t * I)) ∧
          ∀ t : ℝ, c 1 t = (γ (Circle.exp (e * t)) - F0) / (a₀ : ℂ) := by
  intro γ hγ
  -- Step 1: the smooth loop `u = γ ∘ Circle.exp`
  let u : ℝ → ℂ := fun t => γ (Circle.exp t)
  have hu : IsSmoothLoop u := isSmoothLoop_of_isSmoothJordan γ hγ
  -- Step 2: `C¹`-approximation and the straight-line family
  obtain ⟨ε, hε, hSL⟩ := straightLine_loopFamily u hu
  obtain ⟨N, a, happ⟩ := exists_trigPoly_C1_approx u hu.1 hu.2.1 ε hε
  let v₀ : ℝ → ℂ := trigPoly N a
  have hv₀s : ContDiff ℝ ∞ v₀ := contDiff_trigPoly N a
  have hv₀p : ∀ t, v₀ (t + 2 * π) = v₀ t := fun t => trigPoly_periodic N a t
  let L : ℝ → ℝ → ℂ := fun s t => u t + (s : ℂ) * (v₀ t - u t)
  have hL : IsLoopFamily L :=
    hSL v₀ hv₀s hv₀p (fun t => (happ t).2)
  have hL0 : ∀ t, L 0 t = u t := by
    intro t
    show u t + ((0 : ℝ) : ℂ) * (v₀ t - u t) = u t
    simp
  have hL1 : ∀ t, L 1 t = v₀ t := by
    intro t
    show u t + ((1 : ℝ) : ℂ) * (v₀ t - u t) = v₀ t
    simp only [Complex.ofReal_one, one_mul]
    ring
  have hv₀ : IsSmoothLoop v₀ := by
    have h := isSmoothLoop_of_loopFamily hL (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    have hfun : (L 1) = v₀ := funext hL1
    rwa [hfun] at h
  -- Step 3: the Laurent collar
  obtain ⟨ρ, hρ0, hρ1, hΓinj, hΓderiv⟩ := laurent_collar N a hv₀
  let Γ : ℂ → ℂ := laurentPoly N a
  have hΓcirc : ∀ t : ℝ, Γ (Complex.exp (t * I)) = v₀ t := fun t => laurentPoly_exp N a t
  have hΓann : annulus ρ ⊆ {0}ᶜ := by
    intro w hw
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hw0
    rw [hw0] at hw
    simp only [annulus, Set.mem_ofPred_eq, norm_zero] at hw
    linarith [hw.1, hρ0]
  have hΓd : DifferentiableOn ℂ Γ (annulus ρ) :=
    (laurentPoly_differentiableOn N a).mono hΓann
  have hΓcont : ContinuousOn Γ (annulus ρ) := hΓd.continuousOn
  have hΓopen : IsOpen (Γ '' annulus ρ) :=
    isOpen_image_of_differentiableOn_of_injOn (isOpen_annulus ρ) hΓd hΓinj
  -- Step 4: the Jordan domain and the side of the collar
  obtain ⟨D, hDo, hDc, hDb, hDdisj, hDfr, hDext, hDcc, hJ⟩ := hN4 v₀ hv₀
  have hside :=
    hN4b v₀ D hDo hDfr hDdisj hDext Γ ρ hρ0 hρ1 hΓcont hΓinj hΓopen hΓcirc
  rcases hside with hinner | houter
  · -- inner case: `Γ` already has the correct orientation
    obtain ⟨hin, hout⟩ := hinner
    obtain ⟨a₀, F0, e, ha₀, he, c, hc, hc0, hc1⟩ :=
      chain_tail (u := u) (L := L) hL hL0 v₀ hv₀ D hDo hDc hDb hDcc hJ hDfr hDdisj hDext
        Γ ρ hρ0 hρ1 hΓd hΓinj hΓderiv hΓcirc hin hout 1 (Or.inl rfl)
        (fun t => by rw [one_mul]; exact (hL1 t).symm) hN6 hN7 hN8
    exact ⟨a₀, F0, e, ha₀, he, c, hc, hc0, fun t => hc1 t⟩
  · -- outer case: flip the collar
    obtain ⟨houtC, hinD⟩ := houter
    let v : ℝ → ℂ := fun t => v₀ (-t)
    let Γ' : ℂ → ℂ := fun w => Γ w⁻¹
    have hv : IsSmoothLoop v := isSmoothLoop_comp_neg hv₀
    have hflip := flip_collar_data hρ0 hΓd hΓinj hΓderiv
    have hΓ'd : DifferentiableOn ℂ Γ' (annulus ρ) := hflip.1
    have hΓ'i : InjOn Γ' (annulus ρ) := hflip.2.1
    have hΓ'deriv : ∀ w ∈ annulus ρ, deriv Γ' w ≠ 0 := hflip.2.2
    have hΓ'circ : ∀ t : ℝ, Γ' (Complex.exp (t * I)) = v t := by
      intro t
      show Γ ((Complex.exp (t * I))⁻¹) = v₀ (-t)
      have hexp : (Complex.exp (t * I))⁻¹ = Complex.exp ((-t) * I) := by
        rw [← Complex.exp_neg]
        congr 1
        push_cast
        ring
      rw [hexp]
      simpa using hΓcirc (-t)
    have hin : Γ' '' (annulus ρ ∩ ball 0 1) ⊆ D := by
      show (fun w => Γ w⁻¹) '' (annulus ρ ∩ ball 0 1) ⊆ D
      rw [← Set.image_image, inv_image_annulus_inter_ball hρ0 hρ1]
      exact houtC
    have hout : Disjoint (Γ' '' (annulus ρ \ closedBall 0 1)) D := by
      show Disjoint ((fun w => Γ w⁻¹) '' (annulus ρ \ closedBall 0 1)) D
      rw [← Set.image_image, inv_image_annulus_diff_closedBall hρ0 hρ1]
      exact hinD
    have hrange : Set.range v = Set.range v₀ := by
      show Set.range (fun t => v₀ (-t)) = Set.range v₀
      exact range_comp_neg v₀
    have hDfr' : frontier D = range v := by rw [hrange]; exact hDfr
    have hDdisj' : Disjoint D (range v) := by rw [hrange]; exact hDdisj
    have hDext' : range v ⊆ closure (D ∪ range v)ᶜ := by rw [hrange]; exact hDext
    obtain ⟨a₀, F0, e, ha₀, he, c, hc, hc0, hc1⟩ :=
      chain_tail (u := u) (L := L) hL hL0 v hv D hDo hDc hDb hDcc hJ hDfr' hDdisj'
        hDext' Γ' ρ hρ0 hρ1 hΓ'd hΓ'i hΓ'deriv hΓ'circ hin hout (-1) (Or.inr rfl)
        (fun t => by
          show v₀ (-t) = L 1 ((-1 : ℝ) * t)
          rw [show (-1 : ℝ) * t = -t by ring]
          exact (hL1 (-t)).symm) hN6 hN7 hN8
    exact ⟨a₀, F0, e, ha₀, he, c, hc, hc0, fun t => hc1 t⟩

end Work.RPB.B1chain
