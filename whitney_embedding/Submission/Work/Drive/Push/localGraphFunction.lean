import Mathlib
import Submission.Work.Drive.Push.localInverseContDiffOn
import Submission.Work.Drive.Push.graphFunction_of_localSection

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# The local graph function of a smooth map `M^n → ℝ^{2n}` with injective `(π ∘ df)` at a point

For a `C^∞` map `f : M → ℝ^{2n}` from a smoothly charted `n`-manifold, a linear equivalence
`L : ℝ^{2n} ≃ ℝ^n × ℝ^n` such that `v ↦ (L (mfderiv f x₀ v)).1` is injective at `x₀`, and any
`ε > 0`, there are a neighbourhood `O ∋ x₀` on which the first coordinate of `L ∘ f` stays in the
ball of radius `ε` around its value at `x₀`, and a `C^∞` function `h : ℝ^n → ℝ^n` with

  `(L (f x)).2 = h ((L (f x)).1)`  for all `x ∈ O`.

This is the local form of the graph representation of a codimension-`n` sheet: since `n + n = 2n`
the injectivity of the derivative of the first component makes it a local diffeomorphism, so the
second component is locally a function of the first.

## The proof

1. `G := fun x => (L (f x)).1` is `C^∞` and, by the chain rule, `mfderiv G x₀ = P ∘ mfderiv f x₀`
   where `P = fst ∘ L`; hence `mfderiv G x₀` is injective by hypothesis (`hinjG`).
2. `exists_localSection_of_mfderiv_injective` (below, proved from the inverse function theorem via
   a chart of `M`) produces an open `S ∋ G x₀`, an open `U ∋ x₀` and a total `σ : ℝ^n → M` that is
   `C^∞` on `S`, with `G ∘ σ = id` on `S` and `σ ∘ G = id` on `U`.
3. `graphFunction_of_localSection` (a colleague's brick, in `Submission/Work/Drive/Push`) turns this
   data into the required `h`, using a bump function supported in `S`.
-/

namespace Work.Drive.Push

open scoped Manifold ContDiff Topology
open Set Function

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

set_option backward.isDefEq.respectTransparency false in
/-- **The derivative of a chart and of its inverse compose to the identity.**  For a chart `c` of
`M` around `y`, the manifold derivatives `mfderiv c y` and `mfderiv c.symm (c y)` are mutually
inverse.  (This is the content of `mfderiv_comp` applied to `c ∘ c.symm =ᶠ id`.) -/
theorem mfderiv_chart_comp_symm
    (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
    {y : M} (hy : y ∈ c.source)
    (hcsm : ContMDiffAt (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) c y)
    (hsymm : ContMDiffAt (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c y)) :
    (mfderiv (𝓡 n) (𝓡 n) c y) ∘SL (mfderiv (𝓡 n) (𝓡 n) c.symm (c y))
      = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) := by
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hc : MDifferentiableAt (𝓡 n) (𝓡 n) c (c.symm (c y)) := by
    rw [c.left_inv hy]; exact hcsm.mdifferentiableAt hne
  have hs : MDifferentiableAt (𝓡 n) (𝓡 n) c.symm (c y) := hsymm.mdifferentiableAt hne
  have hcomp : mfderiv (𝓡 n) (𝓡 n) (c ∘ c.symm) (c y)
      = (mfderiv (𝓡 n) (𝓡 n) c (c.symm (c y))).comp (mfderiv (𝓡 n) (𝓡 n) c.symm (c y)) :=
    mfderiv_comp (f := c.symm) (x := c y) hc hs
  rw [c.left_inv hy] at hcomp
  have heq : c ∘ c.symm =ᶠ[𝓝 (c y)] id := by
    filter_upwards [c.open_target.mem_nhds (c.map_source hy)] with z hz
    rw [Function.comp_apply, c.right_inv hz]
    rfl
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  exact hcomp.symm

set_option backward.isDefEq.respectTransparency false in
/-- **The local inverse function theorem for manifolds, at a point.**  A `C^∞` map `G : M → ℝ^n`
from a smooth `n`-manifold whose manifold derivative at `x₀` is injective is a local diffeomorphism
at `x₀`: there are an open `S ∋ G x₀`, an open `U ∋ x₀` and a (total) map `σ : ℝ^n → M` that is
`C^∞` on `S`, with `G (σ u) = u` for `u ∈ S` and `σ (G x) = x` for `x ∈ U`.

This is the missing converse direction of `IsLocalDiffeomorphAt` (Mathlib has only the forward
direction).  The proof reads `G` in a chart `c` of `M`: the chart expression `g = G ∘ c.symm` has
invertible Fréchet derivative at `c x₀` because `mfderiv G x₀ = mfderiv g (c x₀) ∘ mfderiv c.symm (c x₀)`
with both factors injective (the second by `mfderiv_chart_comp_symm`), and the Euclidean inverse
function theorem `localInverseContDiffOn` applied to `g` gives a smooth local inverse `σ`, which
`c.symm ∘ σ` transports back to `M`. -/
theorem exists_localSection_of_mfderiv_injective
    (G : M → EuclideanSpace ℝ (Fin n))
    (hG : ContMDiff (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) G)
    (x₀ : M)
    (hinj : Function.Injective (mfderiv (𝓡 n) (𝓡 n) G x₀)) :
    ∃ (S : Set (EuclideanSpace ℝ (Fin n))) (U : Set M)
      (σ : EuclideanSpace ℝ (Fin n) → M),
      IsOpen S ∧ G x₀ ∈ S ∧ IsOpen U ∧ x₀ ∈ U ∧
      (∀ u ∈ S, G (σ u) = u) ∧
      (∀ x ∈ U, σ (G x) = x) ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) σ S := by
  classical
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) x₀ with hcdef
  have hcsrc : x₀ ∈ c.source := mem_chart_source _ _
  have hctgt : c x₀ ∈ c.target := c.map_source hcsrc
  have hcsm : ContMDiffAt (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) c x₀ :=
    contMDiffOn_chart.contMDiffAt (c.open_source.mem_nhds hcsrc)
  have hsmm : ContMDiffAt (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) c.symm (c x₀) :=
    contMDiffOn_chart_symm.contMDiffAt (c.open_target.mem_nhds hctgt)
  have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  -- the chart expression of `G`
  set g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := fun u => G (c.symm u) with hgdef
  have hgsm : ContMDiffOn (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) g c.target :=
    ContMDiffOn.comp (I := 𝓡 n) (I' := 𝓡 n) (I'' := 𝓡 n) (M' := M)
      (f := c.symm) (g := G) (t := Set.univ)
      (hG.contMDiffOn (s := Set.univ)) contMDiffOn_chart_symm (fun _ _ => trivial)
  have hgcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g c.target := hgsm.contDiffOn
  have hgc : g (c x₀) = G x₀ := by rw [hgdef]; simp only []; rw [c.left_inv hcsrc]
  -- the derivative of the chart expression is injective
  have hinjg : Function.Injective (fderiv ℝ g (c x₀)) := by
    have hfdeq : fderiv ℝ g (c x₀)
        = mfderiv (𝓡 n) (𝓡 n) (fun u => G (c.symm u)) (c x₀) := mfderiv_eq_fderiv.symm
    have happ : ∀ v : EuclideanSpace ℝ (Fin n),
        fderiv ℝ g (c x₀) v
          = mfderiv (𝓡 n) (𝓡 n) (fun u => G (c.symm u)) (c x₀) v :=
      fun v => congrArg
        (fun (L : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) => L v) hfdeq
    have hcsinj : Function.Injective (mfderiv (𝓡 n) (𝓡 n) c.symm (c x₀)) :=
      (ContinuousLinearMap.leftInverse_of_comp
        (mfderiv_chart_comp_symm c hcsrc hcsm hsmm)).injective
    have hInj' : Function.Injective
        (mfderiv (𝓡 n) (𝓡 n) (fun u => G (c.symm u)) (c x₀)) := by
      have hcomp : mfderiv (𝓡 n) (𝓡 n) (fun u => G (c.symm u)) (c x₀)
          = (mfderiv (𝓡 n) (𝓡 n) G x₀).comp (mfderiv (𝓡 n) (𝓡 n) c.symm (c x₀)) := by
        have hGd : MDifferentiableAt (𝓡 n) (𝓡 n) G (c.symm (c x₀)) := by
          rw [c.left_inv hcsrc]; exact hG.contMDiffAt.mdifferentiableAt hne
        have h := mfderiv_comp (f := c.symm) (x := c x₀) hGd (hsmm.mdifferentiableAt hne)
        rw [c.left_inv hcsrc] at h
        exact h
      rw [hcomp]
      exact hinj.comp hcsinj
    intro v w hvw
    refine hInj' ?_
    rw [← happ v, ← happ w, hvw]
  -- the inverse function theorem in the chart
  obtain ⟨S, W, σ, hS, hW, hWU, hgpS, hpW, hσsm, hgσ, hσg⟩ :=
    localInverseContDiffOn g c.target c.open_target hgcd (c x₀) hctgt hinjg
  -- shrink `S` so that `σ` maps it into the chart target
  have hσcont : ContinuousAt σ (g (c x₀)) :=
    hσsm.continuousOn.continuousAt (hS.mem_nhds hgpS)
  have hσgp : σ (g (c x₀)) = c x₀ := hσg (c x₀) hpW
  have hmempre : σ ⁻¹' c.target ∈ 𝓝 (g (c x₀)) := by
    refine hσcont.preimage_mem_nhds (c.open_target.mem_nhds ?_)
    rw [hσgp]; exact hctgt
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hmempre
  -- assemble the local section on `M`
  have hGx₀S : G x₀ ∈ S := by rwa [← hgc]
  refine ⟨S ∩ Metric.ball (G x₀) r, c.source ∩ c ⁻¹' W, fun u => c.symm (σ u),
    hS.inter Metric.isOpen_ball, ⟨hGx₀S, ?_⟩, c.isOpen_inter_preimage hW, ⟨hcsrc, hpW⟩, ?_, ?_, ?_⟩
  · rw [← hgc]; exact Metric.mem_ball_self hr
  · intro u hu
    show G (c.symm (σ u)) = u
    exact hgσ u hu.1
  · intro x hx
    show c.symm (σ (G x)) = x
    have hGx : G x = g (c x) := by rw [hgdef]; simp only []; rw [c.left_inv hx.1]
    rw [hGx, hσg (c x) hx.2]
    exact c.left_inv hx.1
  · refine ContMDiffOn.comp (I := 𝓡 n) (I' := 𝓡 n) (I'' := 𝓡 n)
      (f := σ) (g := c.symm) (t := c.target) ?_ ?_ ?_
    · exact contMDiffOn_chart_symm
    · exact hσsm.contMDiffOn.mono inter_subset_left
    · intro u hu
      rw [← hgc] at hu
      exact hrsub hu.2

set_option backward.isDefEq.respectTransparency false in
/-- **The local graph function.**  See the module documentation. -/
theorem localGraphFunction {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (x₀ : M)
    (L : EuclideanSpace ℝ (Fin (2 * n)) ≃L[ℝ]
      (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)))
    (htrans : ∀ v : EuclideanSpace ℝ (Fin n),
      (L (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f x₀ v)).1 = 0 → v = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (O : Set M) (h : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
      IsOpen O ∧ x₀ ∈ O ∧
      (∀ x ∈ O, (L (f x)).1 ∈ Metric.ball ((L (f x₀)).1) ε) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧
      (∀ x ∈ O, (L (f x)).2 = h ((L (f x)).1)) := by
  classical
  -- the first component `P ∘ f` of `L ∘ f`
  set P : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n))).comp
      (L : EuclideanSpace ℝ (Fin (2 * n)) →L[ℝ]
        (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))) with hPdef
  have hPapp : ∀ v : EuclideanSpace ℝ (Fin (2 * n)), P v = (L v).1 := fun _ => rfl
  set G : M → EuclideanSpace ℝ (Fin n) := fun x => P (f x) with hGdef
  have hGsm : ContMDiff (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) G := by
    rw [hGdef]
    exact P.contMDiff.comp hf
  -- its derivative at `x₀` is injective
  have hinj : Function.Injective (mfderiv (𝓡 n) (𝓡 n) G x₀) := by
    have hne : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
    have hPf : MDifferentiableAt (𝓡 (2 * n)) (𝓡 n)
        (fun y : EuclideanSpace ℝ (Fin (2 * n)) => P y) (f x₀) :=
      ((P.contMDiff).contMDiffAt (x := f x₀)).mdifferentiableAt hne
    have hff : MDifferentiableAt (𝓡 n) (𝓡 (2 * n)) f x₀ :=
      ((hf x₀)).mdifferentiableAt hne
    have hcomp : mfderiv (𝓡 n) (𝓡 n) G x₀
        = (mfderiv (𝓡 (2 * n)) (𝓡 n) (fun y => P y) (f x₀)).comp
            (mfderiv (𝓡 n) (𝓡 (2 * n)) f x₀) := by
      rw [hGdef]
      exact mfderiv_comp (f := f) (x := x₀) hPf hff
    have hPmd : mfderiv (𝓡 (2 * n)) (𝓡 n) (fun y => P y) (f x₀) = P := by
      rw [mfderiv_eq_fderiv]
      exact P.hasFDerivAt.fderiv
    rw [hcomp, hPmd]
    have hLP : ∀ x : TangentSpace (𝓡 n) x₀,
        (L (mfderiv (𝓡 n) (𝓡 (2 * n)) f x₀ x)).1
          = (P ∘SL mfderiv (𝓡 n) (𝓡 (2 * n)) f x₀) x := by
      intro x
      rfl
    exact fun v w hvw => by
      have h2 : (P ∘SL mfderiv (𝓡 n) (𝓡 (2 * n)) f x₀) (v - w) = 0 := by
        calc (P ∘SL mfderiv (𝓡 n) (𝓡 (2 * n)) f x₀) (v - w)
            = (P ∘SL mfderiv (𝓡 n) (𝓡 (2 * n)) f x₀) v
              - (P ∘SL mfderiv (𝓡 n) (𝓡 (2 * n)) f x₀) w := map_sub _ _ _
          _ = (P ∘SL mfderiv (𝓡 n) (𝓡 (2 * n)) f x₀) w
              - (P ∘SL mfderiv (𝓡 n) (𝓡 (2 * n)) f x₀) w :=
                congrArg (fun y => y - (P ∘SL mfderiv (𝓡 n) (𝓡 (2 * n)) f x₀) w) hvw
          _ = 0 := sub_self _
      have hkey : (L (mfderiv (𝓡 n) (𝓡 (2 * n)) f x₀ (v - w))).1 = 0 :=
        (hLP (v - w)).trans h2
      exact sub_eq_zero.mp (htrans (v - w) hkey)
  -- the local section of `G`
  obtain ⟨S, U, σ, hS, hGS, hU, hx₀U, hright, hleft, hσsm⟩ :=
    exists_localSection_of_mfderiv_injective G hGsm x₀ hinj
  have hfσ : ContMDiffOn (𝓡 n) (𝓡 (2 * n)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u => f (σ u)) S :=
    ContMDiffOn.comp (I := 𝓡 n) (I' := 𝓡 n) (I'' := 𝓡 (2 * n)) (M' := M)
      (f := σ) (g := f) (t := Set.univ)
      (hf.contMDiffOn (s := Set.univ)) hσsm (fun _ _ => trivial)
  -- the three hypotheses of the brick, restated with `(L (f ·)).1` in place of `G`
  have hGS' : (L (f x₀)).1 ∈ S := by simpa only [hGdef, hPapp] using hGS
  have hright' : ∀ u ∈ S, (L (f (σ u))).1 = u := fun u hu => by
    simpa only [hGdef, hPapp] using hright u hu
  have hleft' : ∀ x ∈ U, σ ((L (f x)).1) = x := fun x hx => by
    simpa only [hGdef, hPapp] using hleft x hx
  -- the smooth graph function
  exact graphFunction_of_localSection f hf L x₀ σ S U hS hGS' hfσ hU hx₀U hright' hleft' ε hε

end Work.Drive.Push
