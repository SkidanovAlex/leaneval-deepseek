import Mathlib
import Submission.Work.Diff.EXT.gen_defs
import Submission.Work.Diff.EXT.pde_splice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary local lemmas for the generic splicing machinery

This file collects the generic (`E`, `F` arbitrary real normed spaces, `ContDiffOn` on an open set)
versions of the elementary lemmas that `Submission/Work/Diff/EXT/pde_splice.lean` proves for
`ℝ × ℝⁿ → ℝᵐ`:

* locality of the spatial `2`-jet (`sJetG_congr`),
* the vertical-slice neighbourhood lemma,
* the two combinatorial lemmas (`pi_single_sum`, `pair_single_sum`) used by the recursion,
* the chain rule `deriv_psi_comp` for a function of a tuple of functions of `(s,x)`,
* a product neighbourhood inside an open subset of `ℝ × E`,
* smoothness of `p ↦ (fderiv ℝ g p).comp inr` on an open set,
* the local Clairaut fact `deriv_sJetG`,
* `AseqG Φ a j` as the `(j+1)`-st time derivative (`AseqG_eq_iteratedDeriv`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
open scoped ContDiff Topology
open Filter

namespace Work.Diff.EXT.gen

open Work.Diff.EXT (sJetG tderivG AseqG SeqG PsiG JG)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The spatial `2`-jet is a local notion: functions that agree near `z` have the same jet at `z`. -/
theorem sJetG_congr {g h : ℝ × E → F} {z : ℝ × E} (hgh : g =ᶠ[nhds z] h) :
    sJetG g z = sJetG h z := by
  have h1 : g z = h z := hgh.eq_of_nhds
  have hcont : Tendsto (fun y : E => (z.1, y)) (nhds z.2) (nhds z) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hslice : (fun y => g (z.1, y)) =ᶠ[nhds z.2] (fun y => h (z.1, y)) :=
    hgh.comp_tendsto hcont
  have h2 : fderiv ℝ (fun y : E => g (z.1, y)) z.2 = fderiv ℝ (fun y : E => h (z.1, y)) z.2 :=
    (hslice.fderiv (𝕜 := ℝ)).eq_of_nhds
  have h3 : fderiv ℝ (fun w : E => fderiv ℝ (fun y : E => g (z.1, y)) w) z.2
      = fderiv ℝ (fun w : E => fderiv ℝ (fun y : E => h (z.1, y)) w) z.2 :=
    ((hslice.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).eq_of_nhds
  simp only [sJetG, h1, h2, h3]

/-- The vertical slice of a neighbourhood of `z` is a neighbourhood of `z.1`. -/
theorem slice_mem_nhds_of_mem_nhds {S : Set (ℝ × E)} {z : ℝ × E} (hS : S ∈ nhds z) :
    {s : ℝ | (s, z.2) ∈ S} ∈ nhds z.1 := by
  have hS' : S ∈ nhds (z.1, z.2) := hS
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp (by rwa [nhds_prod_eq] at hS')
  refine mem_of_superset hU ?_
  intro s hs
  exact hUV ⟨hs, mem_of_mem_nhds hV⟩

/-- Decomposition of a Pi-vector into its single-coordinate components. -/
theorem pi_single_sum {ι J : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid J]
    (v : ι → J) : (∑ i, Pi.single i (v i)) = v := by
  funext k
  simp only [Finset.sum_apply, Pi.single_apply]
  rw [Finset.sum_ite_eq]
  simp

/-- Decomposition of a vector whose first component is zero. -/
theorem pair_single_sum {N : ℕ} {J : Type*} [AddCommMonoid J] (v : Fin N → J) :
    ((0 : E), v) = ∑ i, ((0 : E), Pi.single i (v i)) := by
  apply Prod.ext
  · simp [Prod.fst_sum]
  · rw [Prod.snd_sum]
    exact (pi_single_sum v).symm

/-- Chain rule for a function of a tuple of functions of `(s,x)` evaluated at `(s,z.2)`, with the
inner functions only assumed `C^∞` *at* `z`. -/
theorem deriv_psi_comp {N : ℕ} {J : Type*} [NormedAddCommGroup J] [NormedSpace ℝ J]
    (Ψ : E × (Fin N → J) → F) (hΨ : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (g : Fin N → ℝ × E → J) (z : ℝ × E) (hg : ∀ i, ContDiffAt ℝ (⊤ : ℕ∞) (g i) z) :
    deriv (fun s : ℝ => Ψ (z.2, fun i => g i (s, z.2))) z.1
      = (fderiv ℝ Ψ (z.2, fun i => g i z)) (0, fun i => deriv (fun s => g i (s, z.2)) z.1) := by
  have h1 : HasDerivAt (fun s : ℝ => (fun i => g i (s, z.2)))
      (fun i => deriv (fun s => g i (s, z.2)) z.1) z.1 := by
    rw [hasDerivAt_pi]
    intro i
    have hd : DifferentiableAt ℝ (fun s : ℝ => g i (s, z.2)) z.1 :=
      ((hg i).differentiableAt (by simp)).comp z.1
        (differentiableAt_id.prodMk (differentiableAt_const z.2))
    exact hd.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (z.2, fun i => g i (s, z.2)))
      (0, fun i => deriv (fun s => g i (s, z.2)) z.1) z.1 := by
    have h := (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.2 (fun i => g i (z.1, z.2))).comp_hasDerivAt
      z.1 h1
    simpa [Function.comp_def] using h
  have h3 : HasFDerivAt Ψ (fderiv ℝ Ψ (z.2, fun i => g i z)) (z.2, fun i => g i z) :=
    ((hΨ.differentiable (by simp)).differentiableAt).hasFDerivAt
  have h4 := h3.comp_hasDerivAt z.1 h2
  simpa [Function.comp_def] using h4.deriv

/-- Every open subset of `ℝ × E` contains a product neighbourhood of each of its points. -/
theorem exists_prod_nhds_subset {V : Set (ℝ × E)} (hV : IsOpen V) {p : ℝ × E} (hp : p ∈ V) :
    ∃ ε > 0, ∃ r > 0, Set.Ioo (p.1 - ε) (p.1 + ε) ×ˢ Metric.ball p.2 r ⊆ V := by
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.mp hV p hp
  refine ⟨ρ, hρ, ρ, hρ, ?_⟩
  intro q hq
  apply hsub
  rw [Metric.mem_ball, Prod.dist_eq]
  rcases hq with ⟨hq1, hq2⟩
  rw [Metric.mem_ball] at hq2
  refine max_lt ?_ hq2
  rw [Set.mem_Ioo] at hq1
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hq1.1, hq1.2]

/-- On an open set where `g` is smooth, the map `p ↦ (fderiv ℝ g p).comp inr` is smooth. -/
theorem contDiffAt_fderiv_comp_inr {V : Set (ℝ × E)} (hV : IsOpen V) {g : ℝ × E → F}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g V) {z : ℝ × E} (hz : z ∈ V) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p : ℝ × E => (fderiv ℝ g p).comp (ContinuousLinearMap.inr ℝ ℝ E)) z := by
  have hgat : ContDiffAt ℝ (⊤ : ℕ∞) g z := hg.contDiffAt (hV.mem_nhds hz)
  have hK : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p : ℝ × E => fderiv ℝ (fun y : E => g (p.1, y)) p.2) z := by
    have hun : ContDiffAt ℝ (⊤ : ℕ∞)
        (Function.uncurry (fun (p : ℝ × E) (y : E) => g (p.1, y))) (z, z.2) := by
      rw [show Function.uncurry (fun (p : ℝ × E) (y : E) => g (p.1, y))
          = (fun q : (ℝ × E) × E => g (q.1.1, q.2)) from rfl]
      let L : ((ℝ × E) × E) →L[ℝ] (ℝ × E) :=
        ((ContinuousLinearMap.fst ℝ ℝ E).comp (ContinuousLinearMap.fst ℝ (ℝ × E) E)).prod
          (ContinuousLinearMap.snd ℝ (ℝ × E) E)
      have hL : (fun q : (ℝ × E) × E => g (q.1.1, q.2)) = g ∘ L := rfl
      rw [hL]
      exact hgat.comp (z, z.2) ((ContinuousLinearMap.contDiff L).contDiffAt)
    exact ContDiffAt.fderiv hun contDiffAt_snd (by simp)
  refine hK.congr_of_eventuallyEq ?_
  filter_upwards [hV.mem_nhds hz] with p hp
  exact (Work.Diff.EXT.fderiv_comp_inr_aux ((hg.contDiffAt (hV.mem_nhds hp)).differentiableAt
    (by simp))).symm

/-- **Clairaut for the spatial `2`-jet** (local form): the time derivative of the spatial jet of a
smooth function is the spatial jet of its time derivative. -/
theorem deriv_sJetG {V : Set (ℝ × E)} (hV : IsOpen V) {g : ℝ × E → F}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g V) {z : ℝ × E} (hz : z ∈ V) :
    deriv (fun s : ℝ => sJetG g (s, z.2)) z.1 = sJetG (tderivG g) z := by
  obtain ⟨t, x⟩ := z
  obtain ⟨ε, hε, r, hr, hWV⟩ := exists_prod_nhds_subset (E := E) hV hz
  have hgat : ContDiffAt ℝ (⊤ : ℕ∞) g (t, x) := hg.contDiffAt (hV.mem_nhds hz)
  have hdiff : ∀ p ∈ (Set.Ioo (t - ε) (t + ε) ×ˢ Metric.ball x r), DifferentiableAt ℝ g p :=
    fun p hp => (hg.contDiffAt (hV.mem_nhds (hWV hp))).differentiableAt (by simp)
  set A' : E →L[ℝ] F := fderiv ℝ (fun y : E => tderivG g (t, y)) x with hA'def
  set B' : E →L[ℝ] (E →L[ℝ] F) :=
    fderiv ℝ (fun w : E => fderiv ℝ (fun y : E => tderivG g (t, y)) w) x with hB'def
  set H : ℝ × E → (E →L[ℝ] F) :=
    fun p => (fderiv ℝ g p).comp (ContinuousLinearMap.inr ℝ ℝ E) with hHdef
  have hH2 : ContDiffAt ℝ 2 H (t, x) :=
    (contDiffAt_fderiv_comp_inr hV hg hz).of_le (m := 2) (by norm_num)
  have hHpt : ∀ p ∈ (Set.Ioo (t - ε) (t + ε) ×ˢ Metric.ball x r),
      H p = fderiv ℝ (fun y : E => g (p.1, y)) p.2 :=
    fun p hp => (Work.Diff.EXT.fderiv_comp_inr_aux (hdiff p hp)).symm
  have htmem : t ∈ Set.Ioo (t - ε) (t + ε) := ⟨by linarith, by linarith⟩
  have hxmem : x ∈ Metric.ball x r := by rw [Metric.mem_ball]; simpa using hr
  have hG : HasDerivAt (fun s : ℝ => g (s, x)) (tderivG g (t, x)) t := by
    have hslice : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => g (s, x)) t :=
      ContDiffAt.comp t hgat (contDiffAt_id.prodMk contDiffAt_const)
    exact (hslice.differentiableAt (by simp)).hasFDerivAt.hasDerivAt
  have hA : HasDerivAt (fun s : ℝ => fderiv ℝ (fun y => g (s, y)) x) A' t :=
    hasDerivAt_sliceFDeriv_aux (hgat.of_le (m := 2) (by norm_num))
  have hHw : ∀ w ∈ Metric.ball x r,
      deriv (fun s : ℝ => H (s, w)) t = fderiv ℝ (fun y : E => tderivG g (t, y)) w := by
    intro w hw
    have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ (fun y => g (s, y)) w)
        (fderiv ℝ (fun y : E => deriv (fun s : ℝ => g (s, y)) t) w) t :=
      hasDerivAt_sliceFDeriv_aux
        ((hg.contDiffAt (hV.mem_nhds (hWV ⟨htmem, hw⟩))).of_le (m := 2) (by norm_num))
    have hev : (fun s : ℝ => H (s, w)) =ᶠ[nhds t]
        (fun s : ℝ => fderiv ℝ (fun y => g (s, y)) w) := by
      filter_upwards [isOpen_Ioo.mem_nhds htmem] with s hs
      exact hHpt (s, w) ⟨hs, hw⟩
    exact (h1.congr_of_eventuallyEq hev).deriv
  have hB : HasDerivAt (fun s : ℝ => fderiv ℝ (fun w => fderiv ℝ (fun y => g (s, y)) w) x)
      B' t := by
    have h0 : HasDerivAt (fun s : ℝ => fderiv ℝ (fun w => H (s, w)) x)
        (fderiv ℝ (fun w : E => deriv (fun s : ℝ => H (s, w)) t) x) t :=
      hasDerivAt_sliceFDeriv_aux hH2
    have hval : fderiv ℝ (fun w : E => deriv (fun s : ℝ => H (s, w)) t) x = B' := by
      have hev : (fun w : E => deriv (fun s : ℝ => H (s, w)) t)
          =ᶠ[nhds x] (fun w : E => fderiv ℝ (fun y : E => tderivG g (t, y)) w) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hxmem] with w hw
        exact hHw w hw
      exact EventuallyEq.fderiv_eq hev
    have hfun : (fun s : ℝ => fderiv ℝ (fun w => fderiv ℝ (fun y => g (s, y)) w) x)
        =ᶠ[nhds t] (fun s : ℝ => fderiv ℝ (fun w => H (s, w)) x) := by
      filter_upwards [isOpen_Ioo.mem_nhds htmem] with s hs
      have hevw : (fun w : E => H (s, w))
          =ᶠ[nhds x] (fun w : E => fderiv ℝ (fun y => g (s, y)) w) := by
        filter_upwards [Metric.isOpen_ball.mem_nhds hxmem] with w hw
        exact hHpt (s, w) ⟨hs, hw⟩
      exact (EventuallyEq.fderiv_eq hevw).symm
    have h1 := h0.congr_of_eventuallyEq hfun
    rw [hval] at h1
    exact h1
  have hpair : HasDerivAt
      (fun s : ℝ => (fderiv ℝ (fun y => g (s, y)) x,
        fderiv ℝ (fun w => fderiv ℝ (fun y => g (s, y)) w) x))
      ((A', B') : (E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)) t := hA.prodMk hB
  have hprod : HasDerivAt
      (fun s : ℝ => (g (s, x), (fderiv ℝ (fun y => g (s, y)) x,
        fderiv ℝ (fun w => fderiv ℝ (fun y => g (s, y)) w) x)))
      ((tderivG g (t, x), (A', B')) : F × ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F))) t :=
    hG.prodMk hpair
  have hjet_eq : (fun s : ℝ => sJetG g (s, x)) = fun s =>
      (g (s, x), (fderiv ℝ (fun y => g (s, y)) x,
        fderiv ℝ (fun w => fderiv ℝ (fun y => g (s, y)) w) x)) := by
    funext s
    rfl
  have hderiv :=
    (hprod.congr_of_eventuallyEq (Eventually.of_forall (fun s => congrFun hjet_eq s))).deriv
  rw [hderiv]
  simp only [hA'def, hB'def, sJetG]

/-- The `(n+1)`-st iterated derivative is the derivative of the `n`-th one (generic form). -/
theorem deriv_iteratedDeriv' (n : ℕ) (f : ℝ → F) (s : ℝ) :
    deriv (fun s' => iteratedDeriv n f s') s = iteratedDeriv (n + 1) f s := by
  rw [iteratedDeriv_succ]

/-- `AseqG Φ a j` is the `(j+1)`-st time derivative of `a` on a set where `a` solves the
equation. -/
theorem AseqG_eq_iteratedDeriv (Φ : E × JG E F → F) {a : ℝ × E → F} {S : Set (ℝ × E)}
    (hS : ∀ z ∈ S, S ∈ nhds z)
    (hPDE : ∀ z ∈ S, deriv (fun s => a (s, z.2)) z.1 = Φ (z.2, sJetG a z)) (j : ℕ) :
    ∀ z ∈ S, AseqG Φ a j z = iteratedDeriv (j + 1) (fun s => a (s, z.2)) z.1 := by
  induction j with
  | zero =>
    intro z hz
    simp only [AseqG]
    rw [← hPDE z hz]
    simp [iteratedDeriv_succ', iteratedDeriv_zero]
  | succ j ih =>
    intro z hz
    rw [show AseqG Φ a (j + 1) z = deriv (fun s => AseqG Φ a j (s, z.2)) z.1 from rfl]
    have hev : (fun s : ℝ => AseqG Φ a j (s, z.2))
        =ᶠ[nhds z.1] (fun s : ℝ => iteratedDeriv (j + 1) (fun s' => a (s', z.2)) s) := by
      filter_upwards [slice_mem_nhds_of_mem_nhds (hS z hz)] with s hs
      exact ih (s, z.2) hs
    rw [hev.deriv_eq, deriv_iteratedDeriv']

end Work.Diff.EXT.gen
