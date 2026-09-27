import Mathlib
import Submission.Work.Geo.Radial.Basic
import Submission.Work.Geo.Radial.exists_contDiff_near_of_compact
import Submission.Work.Geo.Radial.ChartImage
import Submission.Work.Geo.Radial.isOpen_image_of_subset
import Submission.Work.Geo.Radial.continuousOn_chartInv
import Submission.Work.Geo.Radial.abs_lt_abs_smul_add
import Submission.Work.Geo.Radial.exists_continuous_closedBall_selfMap
import Submission.Work.Geo.Radial.exists_ocubeAround_avoid
import Submission.Work.Geo.Radial.exists_continuous_separator

namespace Work.Geo.Radial

open Set Metric
open scoped Topology
open Work.Geo.Radial

/-- The closed unit disc of `ℝ^{j+1}`, as a type: the domain of the maps of this file. -/
abbrev Disc (j : ℕ) : Type := ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (j + 1))) (1 : ℝ))

/-- Gluing two within-continuity statements along a set and its complement. -/
theorem continuousAt_of_continuousWithinAt_compl {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {s : Set X} {x : X}
    (h1 : ContinuousWithinAt f s x) (h2 : ContinuousWithinAt f sᶜ x) : ContinuousAt f x := by
  rw [ContinuousAt, nhds_eq_nhdsWithin_sup_nhdsWithin x (Set.union_compl_self s).symm]
  exact Filter.Tendsto.sup h1 h2

/-- If a point is not in the closure of `s`, the filter `𝓝[s] ·` at it is trivial. -/
theorem nhdsWithin_eq_bot_of_notMem_closure {X : Type*} [TopologicalSpace X] {s : Set X} {x : X}
    (h : x ∉ closure s) : 𝓝[s] x = ⊥ :=
  Filter.not_neBot.mp fun hne => h (mem_closure_iff_nhdsWithin_neBot.mpr hne)

/-- Moving the image of a disc off a small chart cube: if `g : D^{j+1} → M` avoids the chart
image of the cube `PL.openCube β₂` on the boundary sphere, then `g` can be changed (without
changing the boundary values) so that its image misses the chart image of a cube
`ocubeAround q ε` around a point `q` with `|q i| ≤ m`.  (`[T2Space M]` is needed: uniqueness of
limits upgrades point-avoidance to neighbourhood-avoidance; the applications have `M` metric.)

Proof route (two steps):
1. *Point avoidance.*  Let `m < β₃ < β₄ < β₂ < 1`, `K := g ⁻¹' (c.toFun '' PL.closedCube β₃)`
   (compact, since `M` is T2 and `PL.closedCube β₃` is compact) and
   `U := g ⁻¹' (c.toFun '' PL.openCube β₂)` (open, `K ⊆ U`, and the boundary sphere is disjoint
   from `U` by `havoid`).  Pick a continuous `λ : D → [0,1]` with `λ = 1` on `K` and `λ = 0` off
   `U` (`exists_continuous_zero_one_of_isClosed`).  Approximate `P ≈ c⁻¹ ∘ g` on the compact set
   `g ⁻¹' (c.toFun '' PL.closedCube β₄)` (`exists_contDiff_near_of_compact`), blend
   `α u = λ u • P u + (1 - λ u) • c⁻¹ (g u)` on `U` and set `ĝ u = c.toFun (α u)` for `u ∈ U`,
   `ĝ u = g u` otherwise (continuous because `λ = 0` on `∂U`).  For `0 < λ u < 1` the value
   `c⁻¹ (g u)` is outside `PL.closedCube β₃`, so some coordinate `i` has `|c⁻¹(g u) i| > β₃`;
   taking the approximation error small enough the same coordinate satisfies
   `|α u i| > m ≥ |q i|`, hence `α u ≠ q`.  For `λ u = 1` the value is `P u`, and
   `Differentiable.dense_compl_range_of_finrank_lt_finrank` applied to `P` (with `j + 1 < n`)
   makes `range P` have dense complement in `ℝⁿ`, so some `q ∈ ocubeAround 0 m` is not in
   `range P`; outside `U` the value `g u` avoids `c.toFun '' PL.openCube β₂`, which contains
   `c.toFun '' ocubeAround q ε` as soon as `ε + m ≤ β₂`.  So `c.toFun q ∉ range ĝ`.
2. *Neighbourhood avoidance.*  The image of `ĝ` is compact and misses the point `c.toFun q`.
   If every `c.toFun '' ccubeAround q (1/k)` met it, choose `u_k` with
   `ĝ u_k ∈ c.toFun '' ccubeAround q (1/k)`; a convergent subsequence `u_{k_j} → u` (the disc is
   compact) gives `c.toFun (y_{k_j}) = ĝ u_{k_j} → ĝ u` with `y_{k_j} → q` (the cubes shrink),
   hence `ĝ u = c.toFun q` by uniqueness of limits in `M` — contradiction.

The intended fully-qualified name is `Work.Geo.Radial.exists_missing_point_t2`. -/
theorem exists_missing_point_t2 {n j : ℕ} (hj : j + 1 < n) {M : Type*} [TopologicalSpace M]
    [T2Space M] (c : PL.CubeChart n M) {β₂ m : ℝ} (hm : 0 < m) (hmβ₂ : m < β₂) (hβ₂ : β₂ < 1)
    (g : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (j + 1))) 1, M))
    (havoid : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (j + 1))) 1,
      g ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ ∉ c.toFun '' PL.openCube β₂) :
    ∃ ĝ : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (j + 1))) 1, M),
      (∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin (j + 1))) 1,
        ĝ ⟨x.1, Metric.sphere_subset_closedBall x.2⟩ =
          g ⟨x.1, Metric.sphere_subset_closedBall x.2⟩) ∧
      ∃ q : EuclideanSpace ℝ (Fin n), (∀ i, |q i| ≤ m) ∧ ∃ ε : ℝ, 0 < ε ∧
        ∀ u : Metric.closedBall (0 : EuclideanSpace ℝ (Fin (j + 1))) 1,
          ĝ u ∉ c.toFun '' ocubeAround q ε := by
  classical
  -- ## numeric parameters
  obtain ⟨β₃, hmβ₃, hβ₃β₂⟩ : ∃ β₃ : ℝ, m < β₃ ∧ β₃ < β₂ :=
    ⟨(m + β₂) / 2, by linarith, by linarith⟩
  have hβ₃1 : β₃ < 1 := lt_trans hβ₃β₂ hβ₂
  set δ : ℝ := min (min ((β₂ - β₃) / 2) ((β₃ - m) / 2)) ((1 - β₂) / 2) with hδdef
  have hδA : δ ≤ (β₂ - β₃) / 2 := by
    rw [hδdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hδB : δ ≤ (β₃ - m) / 2 := by
    rw [hδdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hδC : δ ≤ (1 - β₂) / 2 := by rw [hδdef]; exact min_le_right _ _
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hδβ₃ : δ < β₃ - m := by linarith
  have hδβ₂ : β₂ + δ < 1 := by linarith
  -- ## the sets `W`, `U`, `K`
  set W : Set M := c.toFun '' PL.openCube (n := n) β₂ with hWdef
  set U : Set (Disc j) := (g : Disc j → M) ⁻¹' W with hUdef
  set K : Set (Disc j) :=
    (g : Disc j → M) ⁻¹' (c.toFun '' PL.closedCube (n := n) β₃) with hKdef
  have hmemU : ∀ u : Disc j, u ∈ U ↔ g u ∈ W := by
    intro u; rw [hUdef]; exact Iff.rfl
  have hmemK : ∀ u : Disc j, u ∈ K ↔ g u ∈ c.toFun '' PL.closedCube (n := n) β₃ := by
    intro u; rw [hKdef]; exact Iff.rfl
  have hcube32 : PL.closedCube (n := n) β₃ ⊆ PL.openCube (n := n) β₂ :=
    fun y hy i => lt_of_le_of_lt (hy i) hβ₃β₂
  have hcubeW1 : PL.openCube (n := n) β₂ ⊆ PL.openCube (n := n) 1 :=
    fun y hy i => lt_trans (hy i) hβ₂
  have hcube21 : PL.closedCube (n := n) β₂ ⊆ PL.openCube (n := n) 1 :=
    fun y hy i => lt_of_le_of_lt (hy i) hβ₂
  have hWopen : IsOpen W := by
    rw [hWdef]
    exact isOpen_image_of_subset c (by simpa using isOpen_ocubeAround (0 : PL.E n) β₂) hcubeW1
  have hUopen : IsOpen U := by rw [hUdef]; exact hWopen.preimage g.continuous
  have hKclosed : IsClosed K := by
    rw [hKdef]
    exact (isCompact_image_closedCube c β₃ hβ₃1).isClosed.preimage g.continuous
  have hKU : K ⊆ U := by
    intro u hu
    rw [hmemU u]
    rw [hmemK u] at hu
    exact Set.image_mono hcube32 hu
  obtain ⟨lam, hlamcont, hlamnn, hlamle, hlamzero, hlampos, hlamone⟩ :=
    exists_continuous_separator hUopen hKclosed hKU
  -- ## the chart inverse of `g`
  let Ψ : Disc j → PL.E n := fun u => chartInv c (g u)
  have hΨcontU : ContinuousOn Ψ ((g : Disc j → M) ⁻¹' chartImage c) :=
    (continuousOn_chartInv c).comp g.continuous.continuousOn (fun u hu => hu)
  have hΩopen : IsOpen ((g : Disc j → M) ⁻¹' chartImage c) :=
    (isOpen_chartImage c).preimage g.continuous
  have hclW : closure W ⊆ c.toFun '' PL.closedCube (n := n) β₂ := by
    rw [hWdef]
    refine closure_minimal (Set.image_mono (fun y hy i => le_of_lt (hy i))) ?_
    exact (isCompact_image_closedCube c β₂ hβ₂).isClosed
  have hUΩ : closure U ⊆ (g : Disc j → M) ⁻¹' chartImage c := by
    intro u hu
    have h1 : g u ∈ closure W := by
      refine closure_mono ?_
        ((image_closure_subset_closure_image (s := U) g.continuous) ⟨u, hu, rfl⟩)
      rintro x ⟨v, hv, rfl⟩
      exact (hmemU v).mp hv
    exact Set.image_mono hcube21 (hclW h1)
  have hΨca : ∀ u₀ ∈ closure U, ContinuousAt Ψ u₀ := fun u₀ hu₀ =>
    hΨcontU.continuousAt (hΩopen.mem_nhds (hUΩ hu₀))
  -- ## the smooth approximation
  obtain ⟨ρ, hρcont, hρid⟩ := exists_continuous_closedBall_selfMap (j + 1)
  let F : PL.E (j + 1) → PL.E n := Ψ ∘ ρ
  have hKcomp : IsCompact ((Subtype.val) '' (closure U)) := by
    haveI : CompactSpace (Disc j) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : PL.E (j + 1)) (1 : ℝ))
    exact isClosed_closure.isCompact.image continuous_subtype_val
  have hFcont : ContinuousOn F ((Subtype.val) '' (closure U)) := by
    rintro x ⟨u₀, hu₀, rfl⟩
    have h1 : ContinuousAt Ψ (ρ (u₀ : PL.E (j + 1))) := by
      rw [hρid u₀]; exact hΨca u₀ hu₀
    exact (h1.comp hρcont.continuousAt).continuousWithinAt
  obtain ⟨P, hPdiff, hPapprox⟩ :=
    exists_contDiff_near_of_compact hKcomp F hFcont hδpos
  have hbound : ∀ u : Disc j, u ∈ U → dist (P (u : PL.E (j + 1))) (Ψ u) < δ := by
    intro u hu
    have hmem : (u : PL.E (j + 1)) ∈ (Subtype.val) '' (closure U) :=
      ⟨u, subset_closure hu, rfl⟩
    have hval : F (u : PL.E (j + 1)) = Ψ u := by
      show Ψ (ρ (u : PL.E (j + 1))) = Ψ u
      rw [hρid u]
    have h := hPapprox (u : PL.E (j + 1)) hmem
    rw [hval] at h
    exact h
  -- ## the blend and the modified map
  let α : Disc j → PL.E n :=
    fun u => lam u • P (u : PL.E (j + 1)) + (1 - lam u) • Ψ u
  have hαeq : ∀ u : Disc j, α u = lam u • P (u : PL.E (j + 1)) + (1 - lam u) • Ψ u :=
    fun u => rfl
  have hΨc : ∀ u ∈ U, Ψ u ∈ PL.openCube (n := n) β₂ := by
    intro u hu
    have hgu : g u ∈ c.toFun '' PL.openCube (n := n) β₂ := by
      rw [← hWdef]; exact (hmemU u).mp hu
    have hgu1 : g u ∈ chartImage c := Set.image_mono hcubeW1 hgu
    obtain ⟨y, hy, hyeq⟩ := hgu
    have hmem : Ψ u ∈ PL.openCube (n := n) 1 := chartInv_mem c hgu1
    have hspec : c.toFun (Ψ u) = g u := chartInv_toFun c hgu1
    have hmem1 : y ∈ PL.openCube (n := n) 1 := fun i => lt_trans (hy i) hβ₂
    have hΨy : Ψ u = y := toFun_injOn_openCube c hmem hmem1 (by rw [hspec, hyeq])
    rw [hΨy]; exact hy
  have hPcoord : ∀ u ∈ U, ∀ i, |P (u : PL.E (j + 1)) i - Ψ u i| < δ := by
    intro u hu i
    have h1 : |(P (u : PL.E (j + 1)) - Ψ u) i| ≤ dist (P (u : PL.E (j + 1))) (Ψ u) := by
      rw [dist_eq_norm]
      simpa using PiLp.norm_apply_le (p := 2) (P (u : PL.E (j + 1)) - Ψ u) i
    have h2 : (P (u : PL.E (j + 1)) - Ψ u) i = P (u : PL.E (j + 1)) i - Ψ u i := rfl
    rw [h2] at h1
    exact lt_of_le_of_lt h1 (hbound u hu)
  have hαmem : ∀ u ∈ closure U, α u ∈ PL.openCube (n := n) 1 := by
    intro u hu
    by_cases huU : u ∈ U
    · intro i
      have h1 : |Ψ u i| < β₂ := hΨc u huU i
      have h2 : |P (u : PL.E (j + 1)) i - Ψ u i| < δ := hPcoord u huU i
      have h3 : (α u) i = Ψ u i + lam u * (P (u : PL.E (j + 1)) i - Ψ u i) := by
        rw [hαeq u]
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [h3]
      have h4 : |Ψ u i + lam u * (P (u : PL.E (j + 1)) i - Ψ u i)| ≤
          |Ψ u i| + lam u * |P (u : PL.E (j + 1)) i - Ψ u i| := by
        calc |Ψ u i + lam u * (P (u : PL.E (j + 1)) i - Ψ u i)|
            ≤ |Ψ u i| + |lam u * (P (u : PL.E (j + 1)) i - Ψ u i)| := abs_add_le _ _
          _ = |Ψ u i| + lam u * |P (u : PL.E (j + 1)) i - Ψ u i| := by
              rw [abs_mul, abs_of_nonneg (hlamnn u)]
      have h5 : lam u * |P (u : PL.E (j + 1)) i - Ψ u i| ≤
          |P (u : PL.E (j + 1)) i - Ψ u i| :=
        mul_le_of_le_one_left (abs_nonneg _) (hlamle u)
      linarith
    · have hz : lam u = 0 := hlamzero u huU
      have hαu : α u = Ψ u := by
        rw [hαeq u, hz]; simp
      rw [hαu]
      exact chartInv_mem c (hUΩ hu)
  have hαca : ∀ u₀ ∈ closure U, ContinuousAt α u₀ := by
    intro u₀ hu₀
    have h1 : ContinuousAt (fun u : Disc j => lam u) u₀ := hlamcont.continuousAt
    have h2 : ContinuousAt (fun u : Disc j => P (u : PL.E (j + 1))) u₀ :=
      (hPdiff.continuous.comp continuous_subtype_val).continuousAt
    have h3 : ContinuousAt Ψ u₀ := hΨca u₀ hu₀
    have h4 : ContinuousAt
        (fun u : Disc j => lam u • P (u : PL.E (j + 1)) + (1 - lam u) • Ψ u) u₀ :=
      (h1.smul h2).add ((continuousAt_const.sub h1).smul h3)
    rw [show α = fun u : Disc j => lam u • P (u : PL.E (j + 1)) + (1 - lam u) • Ψ u from rfl]
    exact h4
  have hopen1 : IsOpen (PL.openCube (n := n) 1) := by
    simpa [ocubeAround_zero] using isOpen_ocubeAround (0 : PL.E n) 1
  have hcca : ∀ u₀ ∈ closure U, ContinuousAt (fun u : Disc j => c.toFun (α u)) u₀ := by
    intro u₀ hu₀
    have hcf : ContinuousAt c.toFun (α u₀) :=
      c.cont.continuousAt (hopen1.mem_nhds (hαmem u₀ hu₀))
    exact hcf.comp (hαca u₀ hu₀)
  let ĝfun : Disc j → M := fun u => if u ∈ closure U then c.toFun (α u) else g u
  have hĝeq : ∀ u : Disc j, ĝfun u = if u ∈ closure U then c.toFun (α u) else g u :=
    fun u => rfl
  have hαval : ∀ u₀ ∈ closure U, u₀ ∉ U → c.toFun (α u₀) = g u₀ := by
    intro u₀ hu₀ huU
    have hz : lam u₀ = 0 := hlamzero u₀ huU
    have hαu : α u₀ = Ψ u₀ := by rw [hαeq u₀, hz]; simp
    rw [hαu]
    exact chartInv_toFun c (hUΩ hu₀)
  have hĝ_off : ∀ u₀ : Disc j, u₀ ∉ U → ĝfun u₀ = g u₀ := by
    intro u₀ huU
    rw [hĝeq u₀]
    by_cases hcl : u₀ ∈ closure U
    · rw [if_pos hcl]; exact hαval u₀ hcl huU
    · rw [if_neg hcl]
  have hĝcont : Continuous ĝfun := by
    rw [continuous_iff_continuousAt]
    intro u₀
    by_cases hU : u₀ ∈ U
    · have hcl : u₀ ∈ closure U := subset_closure hU
      have hev : ĝfun =ᶠ[𝓝 u₀] (fun u : Disc j => c.toFun (α u)) :=
        Filter.eventually_of_mem (hUopen.mem_nhds hU)
          (fun u hu => by rw [hĝeq u, if_pos (subset_closure hu)])
      exact (hcca u₀ hcl).congr_of_eventuallyEq hev
    · by_cases hcl : u₀ ∈ closure U
      · have h1 : ContinuousWithinAt ĝfun U u₀ :=
          ((hcca u₀ hcl).continuousWithinAt).congr
            (fun y hy => by rw [hĝeq y, if_pos (subset_closure hy)])
            (by rw [hĝeq u₀, if_pos hcl])
        have h2 : ContinuousWithinAt ĝfun Uᶜ u₀ :=
          ((g.continuous.continuousAt).continuousWithinAt).congr
            (fun y hy => hĝ_off y hy) (hĝ_off u₀ hU)
        exact continuousAt_of_continuousWithinAt_compl h1 h2
      · have hev : ĝfun =ᶠ[𝓝 u₀] g :=
          Filter.eventually_of_mem (isClosed_closure.isOpen_compl.mem_nhds hcl)
            (fun u hu => by rw [hĝeq u, if_neg hu])
        exact (g.continuous.continuousAt).congr_of_eventuallyEq hev
  -- ## the point to avoid
  have hPdense : Dense (Set.range P)ᶜ :=
    Differentiable.dense_compl_range_of_finrank_lt_finrank (hPdiff.differentiable (by simp)) (by
      rw [finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]; exact hj)
  obtain ⟨q, hqcompl, hqocube⟩ :=
    hPdense.exists_mem_open (isOpen_ocubeAround (0 : PL.E n) m) ⟨0, by intro i; simpa using hm⟩
  have hqnotP : q ∉ Set.range P := hqcompl
  have hqle : ∀ i, |q i| ≤ m := by
    intro i
    have h : |q i - (0 : PL.E n) i| < m := hqocube i
    simpa using le_of_lt h
  have hq1 : q ∈ PL.openCube (n := n) 1 := fun i => lt_of_le_of_lt (hqle i) (lt_trans hmβ₂ hβ₂)
  have hqopen : q ∈ PL.openCube (n := n) β₂ := fun i => lt_of_le_of_lt (hqle i) hmβ₂
  have hqW : c.toFun q ∈ W := by rw [hWdef]; exact ⟨q, hqopen, rfl⟩
  have hpoint : ∀ u : Disc j, ĝfun u ≠ c.toFun q := by
    intro u
    by_cases hU : u ∈ U
    · have hαne : α u ≠ q := by
        by_cases hl1 : lam u = 1
        · have heq : α u = P (u : PL.E (j + 1)) := by
            rw [hαeq u, hl1]; simp
          intro hcon
          exact hqnotP ⟨(u : PL.E (j + 1)), heq ▸ hcon⟩
        · have hlt1 : lam u < 1 := lt_of_le_of_ne (hlamle u) hl1
          have hnotK : u ∉ K := fun hK => (ne_of_lt hlt1) (hlamone u hK)
          have hgnin : g u ∉ c.toFun '' PL.closedCube (n := n) β₃ :=
            fun h => hnotK ((hmemK u).mpr h)
          have hgu1 : g u ∈ chartImage c :=
            Set.image_mono hcubeW1 (by rw [← hWdef]; exact (hmemU u).mp hU)
          have hΨnin : Ψ u ∉ PL.closedCube (n := n) β₃ := fun hin =>
            hgnin ⟨Ψ u, hin, chartInv_toFun c hgu1⟩
          obtain ⟨i, hi⟩ : ∃ i : Fin n, β₃ < |Ψ u i| := by
            have h1 : ¬ ∀ i : Fin n, |Ψ u i| ≤ β₃ := hΨnin
            obtain ⟨i, hi⟩ := not_forall.mp h1
            exact ⟨i, not_le.mp hi⟩
          have hlt : |q i| < |(α u) i| := by
            have h := abs_lt_abs_smul_add hδβ₃ (hlamnn u) (hlamle u) hqle (hPcoord u hU) hi
            show |q i| < |(lam u • P (u : PL.E (j + 1)) + (1 - lam u) • Ψ u) i|
            exact h
          intro hcon
          rw [hcon] at hlt
          exact lt_irrefl _ hlt
      have hα1 : α u ∈ PL.openCube (n := n) 1 := hαmem u (subset_closure hU)
      have hcg : c.toFun (α u) ≠ c.toFun q :=
        fun h => hαne (toFun_injOn_openCube c hα1 hq1 h)
      rw [hĝeq u, if_pos (subset_closure hU)]
      exact hcg
    · have hgut : g u ∉ W := fun hcon => hU ((hmemU u).mpr hcon)
      have hne : g u ≠ c.toFun q := fun h => hgut (h ▸ hqW)
      rw [hĝ_off u hU]
      exact hne
  refine ⟨⟨ĝfun, hĝcont⟩, ?_, q, hqle, ?_⟩
  · intro x
    have hxU : (⟨x.1, Metric.sphere_subset_closedBall x.2⟩ : Disc j) ∉ U :=
      fun hcon => havoid x ((hmemU _).mp hcon)
    exact hĝ_off _ hxU
  · refine exists_ocubeAround_avoid c ⟨ĝfun, hĝcont⟩ hq1 ?_
    rintro ⟨u, hu⟩
    exact hpoint u hu

end Work.Geo.Radial
