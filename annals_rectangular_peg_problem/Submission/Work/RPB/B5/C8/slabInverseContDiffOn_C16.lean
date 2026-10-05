import Mathlib
import Submission.Work.RPB.B5.C12.slabInverseContDiffOn_C12
import Submission.Work.RPB.B3.UniformInverseAux

/-!
# `Work.RPB.B5.C8.slabInverseContDiffOn_C16`

The order-`16` version of `Work.RPB.B5.slabInverseContDiffOn` (and of
`Work.RPB.B5.C12.slabInverseContDiffOn_C12`): the classical-`choose` inverse
`inverseR S ε₀ τ t σ` of the family `ρ ↦ S τ t ρ` is `C¹⁶` on the slab
`[0,1] × ℝ × (-(δ ε₀), δ ε₀)`.  The proof is the inverse function theorem applied to the local
diffeomorphism `Φ(τ,t,ρ) = (τ, t, S τ t ρ)`, exactly as in the `C⁸` and `C¹²` cases; nothing in the
argument depends on the numerical value `8` or `12`.
-/

open Set Filter
open scoped ContDiff Topology

set_option linter.unusedVariables false

namespace Work.RPB.B5.C8

noncomputable section

open Work.RPB.B3

/-- Coordinate formula for a continuous linear functional on `ℝ × (ℝ × ℝ)`: it is the sum of its
three partial evaluations. -/
private lemma clm_apply_coord (T : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ) (v : ℝ × (ℝ × ℝ)) :
    T v = v.1 * T (1, (0, 0)) + v.2.1 * T (0, (1, 0)) + v.2.2 * T (0, (0, 1)) := by
  have hv : v = v.1 • (1, (0, 0)) + v.2.1 • (0, (1, 0)) + v.2.2 • (0, (0, 1)) := by
    ext <;> simp
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, smul_eq_mul]

/-- The differential of `(τ, t, ρ) ↦ (τ, t, S τ t ρ)` at a point where `∂_ρ S ≠ 0`. -/
private def Lfun (DS : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ) : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × (ℝ × ℝ)) :=
  (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).prod
    (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).prod DS)

private lemma Lfun_apply (DS : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ) (v : ℝ × (ℝ × ℝ)) :
    Lfun DS v = (v.1, (v.2.1, DS v)) := rfl

private lemma Lfun_ker (DS : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ) (hc : DS (0, (0, 1)) ≠ 0) :
    (Lfun DS).ker = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  have hv0 : Lfun DS v = 0 := by
    rw [LinearMap.mem_ker] at hv
    simpa using hv
  rw [Lfun_apply] at hv0
  have hv1 : v.1 = 0 := by
    have h := congr_arg Prod.fst hv0
    simpa using h
  have hv2 : v.2.1 = 0 := by
    have h := congr_arg (fun t => t.2.1) hv0
    simpa using h
  have hD : DS v = 0 := by
    have h := congr_arg (fun t => t.2.2) hv0
    simpa using h
  have h2 : v.2.2 = 0 := by
    have hc1 := clm_apply_coord DS v
    rw [hD, hv1, hv2] at hc1
    have : v.2.2 * DS (0, (0, 1)) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hc
  exact Prod.ext hv1 (Prod.ext hv2 h2)

private lemma Lfun_range (DS : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ) (hc : DS (0, (0, 1)) ≠ 0) :
    (Lfun DS).range = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro w
  rw [LinearMap.mem_range]
  refine ⟨(w.1, (w.2.1, (w.2.2 - DS (w.1, (w.2.1, 0))) / DS (0, (0, 1)))), ?_⟩
  change Lfun DS (w.1, (w.2.1, (w.2.2 - DS (w.1, (w.2.1, 0))) / DS (0, (0, 1)))) = w
  rw [Lfun_apply]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · change DS (w.1, (w.2.1, (w.2.2 - DS (w.1, (w.2.1, 0))) / DS (0, (0, 1)))) = w.2.2
      have hcoord := clm_apply_coord DS
        (w.1, (w.2.1, (w.2.2 - DS (w.1, (w.2.1, 0))) / DS (0, (0, 1))))
      have hbase := clm_apply_coord DS (w.1, (w.2.1, 0))
      simp only at hcoord hbase
      rw [hcoord, hbase]
      field_simp
      ring

/-- The `ρ`-partial derivative of `S` is the last coordinate of the F-derivative of `S`
regarded as a function on `ℝ × (ℝ × ℝ)`. -/
private lemma fderiv_Sfun_rho (S : ℝ → ℝ → ℝ → ℝ)
    (hS : ContDiff ℝ 16 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2))
    (p : ℝ × (ℝ × ℝ)) :
    fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) p (0, (0, 1))
      = deriv (fun ρ => S p.1 p.2.1 ρ) p.2.2 := by
  have hSfd : HasFDerivAt (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)
      (fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) p) p :=
    (hS.differentiable (by norm_num) p).hasFDerivAt
  have hm : HasFDerivAt (fun r : ℝ => (p.1, (p.2.1, r)))
      ((0 : ℝ →L[ℝ] ℝ).prod ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ))) p.2.2 := by
    simpa using (hasFDerivAt_const (p.1 : ℝ) p.2.2).prodMk
      ((hasFDerivAt_const (p.2.1 : ℝ) p.2.2).prodMk (hasFDerivAt_id (p.2.2 : ℝ)))
  have hcomp := hSfd.comp p.2.2 hm
  rw [deriv]
  have hslice : (fun ρ : ℝ => S p.1 p.2.1 ρ)
      = (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) ∘ (fun r : ℝ => (p.1, (p.2.1, r))) := rfl
  rw [hslice, hcomp.fderiv]
  simp

theorem slabInverseContDiffOn_C16 (S : ℝ → ℝ → ℝ → ℝ)
    (hS : ContDiff ℝ 16 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2))
    (ε₀ δ : ℝ) (hε₀ : 0 < ε₀) (hδ : 0 < δ)
    (hderiv : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ ρ ∈ Set.Ioo (-ε₀) ε₀,
        deriv (fun ρ => S τ t ρ) ρ ≠ 0)
    (hcover : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, ∀ σ ∈ Set.Ioo (-(δ*ε₀)) (δ*ε₀),
        ∃! ρ, ρ ∈ Set.Ioo (-ε₀) ε₀ ∧ S τ t ρ = σ) :
    ContDiffOn ℝ 16 (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B3.inverseR S ε₀ z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-(δ*ε₀)) (δ*ε₀)) := by
  set U : Set (ℝ × (ℝ × ℝ)) :=
    Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-(δ*ε₀)) (δ*ε₀) with hU
  refine contDiffOn_of_locally_contDiffOn (fun q hq => ?_)
  have hq' := hq
  rw [hU] at hq'
  simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, Set.mem_Ioo, true_and] at hq'
  obtain ⟨hqτ, hqσ⟩ := hq'
  obtain ⟨ρ₀, hρ₀, hρ₀uniq⟩ := hcover q.1 hqτ q.2.1 q.2.2 hqσ
  set p : ℝ × (ℝ × ℝ) := (q.1, (q.2.1, ρ₀)) with hp
  set DS : (ℝ × (ℝ × ℝ)) →L[ℝ] ℝ :=
      fderiv ℝ (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) p with hDS
  have hc : DS (0, (0, 1)) ≠ 0 := by
    rw [hDS, fderiv_Sfun_rho S hS p, hp]
    exact hderiv q.1 hqτ q.2.1 ρ₀ hρ₀.1
  set Φ : (ℝ × (ℝ × ℝ)) → (ℝ × (ℝ × ℝ)) :=
      fun v => (v.1, (v.2.1, S v.1 v.2.1 v.2.2)) with hΦdef
  have hΦp : Φ p = q := by
    rw [hΦdef, hp]
    show (q.1, (q.2.1, S q.1 q.2.1 ρ₀)) = q
    rw [hρ₀.2]
  have hΦcont : ContDiff ℝ 16 Φ := by
    rw [hΦdef]
    have h1 : ContDiff ℝ 16 (fun v : ℝ × (ℝ × ℝ) => v.1) := by fun_prop
    have h2 : ContDiff ℝ 16 (fun v : ℝ × (ℝ × ℝ) => v.2.1) := by fun_prop
    exact ContDiff.prodMk h1 (ContDiff.prodMk h2 hS)
  have hΦcd : ContDiffAt ℝ 16 Φ p := hΦcont.contDiffAt
  have hΦdiff : HasFDerivAt Φ (Lfun DS) p := by
    rw [hΦdef]
    have h1 : HasFDerivAt (fun v : ℝ × (ℝ × ℝ) => v.1)
        (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) p :=
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).hasFDerivAt
    have h2 : HasFDerivAt (fun v : ℝ × (ℝ × ℝ) => v.2.1)
        ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) p :=
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt
    have h3 : HasFDerivAt (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2) DS p := by
      rw [hDS]; exact (hS.differentiable (by norm_num) p).hasFDerivAt
    exact h1.prodMk (h2.prodMk h3)
  have hn : (16 : ℕ∞ω) ≠ 0 := by norm_num
  let Φe : (ℝ × (ℝ × ℝ)) ≃L[ℝ] (ℝ × (ℝ × ℝ)) :=
    ContinuousLinearEquiv.ofBijective (Lfun DS) (Lfun_ker DS hc) (Lfun_range DS hc)
  have hΦe_coe : (Φe : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × (ℝ × ℝ))) = Lfun DS := by
    simp only [Φe]
    exact ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hΦdiff' : HasFDerivAt Φ (Φe : (ℝ × (ℝ × ℝ)) →L[ℝ] (ℝ × (ℝ × ℝ))) p := by
    rw [hΦe_coe]; exact hΦdiff
  let g : (ℝ × (ℝ × ℝ)) → (ℝ × (ℝ × ℝ)) := hΦcd.localInverse hΦdiff' hn
  have hg_cd : ContDiffAt ℝ 16 g (Φ p) := by
    simp only [g]; exact ContDiffAt.to_localInverse hΦcd hΦdiff' hn
  have hg_img : g (Φ p) = p := by
    simp only [g]; exact ContDiffAt.localInverse_apply_image hΦcd hΦdiff' hn
  have hg_right : ∀ᶠ y in 𝓝 (Φ p), Φ (g y) = y := by
    simp only [g, ContDiffAt.localInverse]
    exact HasStrictFDerivAt.eventually_right_inverse (hΦcd.hasStrictFDerivAt' hΦdiff' hn)
  have hproj_cd : ContDiff ℝ 16 (fun z : ℝ × (ℝ × ℝ) => z.2.2) := by fun_prop
  have hgval_cont : ContinuousAt (fun y : ℝ × (ℝ × ℝ) => (g y).2.2) (Φ p) :=
    hproj_cd.continuous.continuousAt.comp hg_cd.continuousAt
  have hgval_at : (g (Φ p)).2.2 = ρ₀ := by
    rw [hg_img, hp]
  have h2 : ∀ᶠ y in 𝓝 (Φ p), (g y).2.2 ∈ Set.Ioo (-ε₀) ε₀ :=
    hgval_cont.preimage_mem_nhds (isOpen_Ioo.mem_nhds (by rw [hgval_at]; exact hρ₀.1))
  obtain ⟨u₁, hu₁, hu₁cd⟩ : ∃ u ∈ 𝓝 (Φ p), ContDiffOn ℝ 16 g u :=
    hg_cd.contDiffOn (by norm_num) (by intro h; simp at h)
  have hev : ∀ᶠ y in 𝓝 (Φ p), (g y).2.2 ∈ Set.Ioo (-ε₀) ε₀ ∧ Φ (g y) = y ∧ y ∈ u₁ :=
    h2.and (hg_right.and hu₁)
  rw [Filter.eventually_iff] at hev
  obtain ⟨w, hwsub, hwopen, hwmem⟩ := mem_nhds_iff.mp hev
  refine ⟨w, hwopen, ?_, ?_⟩
  · rw [← hΦp]; exact hwmem
  · have hwu₁ : w ⊆ u₁ := fun y hy => (hwsub hy).2.2
    have hgOn : ContDiffOn ℝ 16 g w := hu₁cd.mono hwu₁
    have hgc : ContDiffOn ℝ 16 (fun y : ℝ × (ℝ × ℝ) => (g y).2.2) w :=
      hproj_cd.contDiffOn.comp hgOn (mapsTo_univ g w)
    have heqon : ∀ y ∈ U ∩ w,
        (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B3.inverseR S ε₀ z.1 z.2.1 z.2.2) y = (g y).2.2 := by
      intro y hy
      obtain ⟨hyU, hyw⟩ := hy
      have hyU' := hyU
      rw [hU] at hyU'
      simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, Set.mem_Ioo, true_and] at hyU'
      obtain ⟨hyτ, hyσ⟩ := hyU'
      obtain ⟨ρ, hρprops, hρuniq⟩ := hcover y.1 hyτ y.2.1 y.2.2 hyσ
      have hgy := (hwsub hyw).2.1
      have hgvalmem : (g y).2.2 ∈ Set.Ioo (-ε₀) ε₀ := (hwsub hyw).1
      have hgy1 : (g y).1 = y.1 := by
        have h := congr_arg Prod.fst hgy
        simpa [hΦdef] using h
      have hgy2 : (g y).2.1 = y.2.1 := by
        have h := congr_arg (fun t => t.2.1) hgy
        simpa [hΦdef] using h
      have hgyS : S (g y).1 (g y).2.1 (g y).2.2 = y.2.2 := by
        have h := congr_arg (fun t => t.2.2) hgy
        simpa [hΦdef] using h
      rw [hgy1, hgy2] at hgyS
      exact inverseR_eq hgvalmem hgyS
        (fun ρ' h1 h2' => (hρuniq ρ' ⟨h1, h2'⟩).trans
          (hρuniq (g y).2.2 ⟨hgvalmem, hgyS⟩).symm)
    exact (hgc.mono Set.inter_subset_right).congr heqon

end

end Work.RPB.B5.C8
