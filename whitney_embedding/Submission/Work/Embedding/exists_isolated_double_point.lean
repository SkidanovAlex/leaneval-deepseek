import Mathlib

namespace Work.Embedding

open scoped Manifold ContDiff
open Filter Topology

/-- If two sheets of a smooth map `g : M → ℝ^{2n}` meet at a double point `g x₀ = g y₀`
(`x₀ ≠ y₀`) with complementary tangent images
(`range (mfderiv g x₀) ⊔ range (mfderiv g y₀) = ⊤`), then that double point is isolated: there are
open neighbourhoods `U ∋ x₀`, `V ∋ y₀` with `U ∩ V = ∅` such that `g x = g y` for `x ∈ U`,
`y ∈ V` forces `x = x₀` and `y = y₀`.

Suggested proof: `F (x, y) = g x - g y` on the product manifold `M × M` (dimension `2n`) is smooth
with `F (x₀,y₀) = 0`; its `mfderiv` at `(x₀,y₀)` is `(u,v) ↦ mfderiv g x₀ u - mfderiv g y₀ v`
(Mathlib's `mfderiv_prodMk`/`mfderiv_fst`/`mfderiv_snd` together with `h0`), which is *surjective*
because its range is `range (mfderiv g x₀) ⊔ range (mfderiv g y₀) = ⊤`.  Since domain and target are
both `2n`-dimensional, it is bijective, so by the inverse function theorem `F` is a local
diffeomorphism (e.g. `HasStrictFDerivAt.localInverse`/`IsLocalDiffeomorphAt`) and hence locally
injective near `(x₀,y₀)`.  Shrink the resulting product neighbourhood to disjoint `U`, `V` using
`T2Space M` and `x₀ ≠ y₀`. -/
theorem exists_isolated_double_point {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M]
    (g : M → EuclideanSpace ℝ (Fin (2*n)))
    (hg : ContMDiff (𝓡 n) (𝓡 (2*n)) ∞ g)
    {x₀ y₀ : M} (hxy : x₀ ≠ y₀) (h0 : g x₀ = g y₀)
    (htrans : (mfderiv (𝓡 n) (𝓡 (2*n)) g x₀).range ⊔ (mfderiv (𝓡 n) (𝓡 (2*n)) g y₀).range = ⊤) :
    ∃ U V : Set M, IsOpen U ∧ IsOpen V ∧ x₀ ∈ U ∧ y₀ ∈ V ∧ U ∩ V = ∅ ∧
      ∀ x ∈ U, ∀ y ∈ V, g x = g y → x = x₀ ∧ y = y₀ := by
  -- Two points of the product manifold, and the difference map.
  let p₀ : M × M := (x₀, y₀)
  let F : M × M → EuclideanSpace ℝ (Fin (2*n)) := fun p => g p.1 - g p.2
  -- Charts around `x₀` and `y₀`, and the coordinate expression of `g` in these charts.
  let χ : PartialEquiv (M × M) (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
    extChartAt ((𝓡 n).prod (𝓡 n)) p₀
  let χx : PartialEquiv M (EuclideanSpace ℝ (Fin n)) := extChartAt (𝓡 n) x₀
  let χy : PartialEquiv M (EuclideanSpace ℝ (Fin n)) := extChartAt (𝓡 n) y₀
  let Φx : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2*n)) :=
    writtenInExtChartAt (𝓡 n) (𝓡 (2*n)) x₀ g
  let Φy : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2*n)) :=
    writtenInExtChartAt (𝓡 n) (𝓡 (2*n)) y₀ g
  let ax : EuclideanSpace ℝ (Fin n) := χx x₀
  let ay : EuclideanSpace ℝ (Fin n) := χy y₀
  let a : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) := (ax, ay)
  -- The coordinate expression of `F` in the product chart: `(u, v) ↦ Φx u - Φy v`.
  let Ψ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2*n)) :=
    fun u => Φx u.1 - Φy u.2
  -- The derivatives of `g` at `x₀` and `y₀`, and their difference map on `E × E`.
  let Dx : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2*n)) :=
    mfderiv (𝓡 n) (𝓡 (2*n)) g x₀
  let Dy : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (2*n)) :=
    mfderiv (𝓡 n) (𝓡 (2*n)) g y₀
  let D : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2*n)) :=
    Dx.comp (ContinuousLinearMap.fst ℝ _ _) - Dy.comp (ContinuousLinearMap.snd ℝ _ _)
  -- The model with corners `𝓡 n` is the identity model, so its range is everything.
  have hrange : Set.range ((𝓡 n) : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) =
      Set.univ := ModelWithCorners.range_eq_univ _
  have hrangep : Set.range (((𝓡 n).prod (𝓡 n)) :
      ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) →
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) = Set.univ := by
    rw [ModelWithCorners.range_prod, hrange, Set.univ_prod_univ]
  -- Smoothness of the two coordinate expressions, read off from `hg` in the preferred charts.
  have hΦx_cd : ContDiffAt ℝ ∞ Φx ax := by
    have h := (contMDiffAt_iff.mp (hg x₀)).2
    rw [hrange, contDiffWithinAt_univ] at h
    exact h
  have hΦy_cd : ContDiffAt ℝ ∞ Φy ay := by
    have h := (contMDiffAt_iff.mp (hg y₀)).2
    rw [hrange, contDiffWithinAt_univ] at h
    exact h
  -- Their derivatives are the manifold derivatives of `g`.
  have hΦx_fd : HasFDerivAt Φx Dx ax := by
    have h := ((hg x₀).mdifferentiableAt (by norm_num)).hasMFDerivAt.2
    rw [hrange] at h
    exact h.hasFDerivAt (by simp)
  have hΦy_fd : HasFDerivAt Φy Dy ay := by
    have h := ((hg y₀).mdifferentiableAt (by norm_num)).hasMFDerivAt.2
    rw [hrange] at h
    exact h.hasFDerivAt (by simp)
  -- Hence `Ψ` is smooth at `a` with derivative `D`.
  have hΨ_cd : ContDiffAt ℝ ∞ Ψ a := by
    have h1 := hΦx_cd.comp a contDiffAt_fst
    have h2 := hΦy_cd.comp a contDiffAt_snd
    exact h1.sub h2
  have hΨ_fd : HasFDerivAt Ψ D a := by
    have h1 : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => Φx u.1)
        (Dx.comp (ContinuousLinearMap.fst ℝ _ _)) a := by fun_prop
    have h2 : HasFDerivAt (fun u : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => Φy u.2)
        (Dy.comp (ContinuousLinearMap.snd ℝ _ _)) a := by fun_prop
    exact h1.sub h2
  -- `D` is bijective: it is surjective because the two tangent ranges span the target, and the
  -- dimensions match (`2n = n + n`).
  have htrans' : Dx.range ⊔ Dy.range = ⊤ := htrans
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin (2*n))) := by
    simp only [Module.finrank_prod, finrank_euclideanSpace, Fintype.card_fin]
    omega
  have hDsurj : Function.Surjective D := by
    intro w
    have hw : w ∈ Dx.range ⊔ Dy.range := by rw [htrans']; exact Submodule.mem_top
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hw
    obtain ⟨u', rfl⟩ := LinearMap.mem_range.mp hu
    obtain ⟨v', rfl⟩ := LinearMap.mem_range.mp hv
    refine ⟨(u', -v'), ?_⟩
    simpa [D] using huv
  have hker : D.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hDsurj
  have htop : D.range = ⊤ := LinearMap.range_eq_top.mpr hDsurj
  let e : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (2*n)) := ContinuousLinearEquiv.ofBijective D hker htop
  let eD : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →L[ℝ]
      EuclideanSpace ℝ (Fin (2*n)) := e
  have hΨ_fd' : HasFDerivAt Ψ eD a := by
    rw [show eD = D from ContinuousLinearEquiv.coe_ofBijective D hker htop]
    exact hΨ_fd
  -- The inverse function theorem: `Ψ` has an invertible strict derivative at `a`.
  have hS : HasStrictFDerivAt Ψ eD a := hΨ_cd.hasStrictFDerivAt' hΨ_fd' (by norm_num)
  obtain ⟨S, hSmem, hSinj⟩ := Filter.eventually_iff_exists_mem.mp hS.eventually_left_inverse
  obtain ⟨S₀, hS₀sub, hS₀open, haS₀⟩ := mem_nhds_iff.mp hSmem
  -- In particular `Ψ` is injective on a neighbourhood of `a`.
  have hS₀inj : ∀ u ∈ S₀, ∀ v ∈ S₀, Ψ u = Ψ v → u = v := by
    intro u hu v hv huv
    have h1 := hSinj u (hS₀sub hu)
    have h2 := hSinj v (hS₀sub hv)
    rw [← h1, ← h2, huv]
  -- Pull the neighbourhood back to `M × M`.
  let W : Set (M × M) := χ.source ∩ χ ⁻¹' S₀
  have hWopen : IsOpen W := by
    simp only [W, χ]
    exact (continuousOn_extChartAt p₀).isOpen_inter_preimage (isOpen_extChartAt_source p₀) hS₀open
  have hχp₀ : χ p₀ = a := by
    simp only [χ, χx, χy, a, ax, ay, p₀, extChartAt_prod, PartialEquiv.prod_coe]
  have hi : ∀ u, Φx u = g (χx.symm u) := by
    intro u
    simp only [Φx, χx, writtenInExtChartAt, Function.comp_apply]
    rfl
  have hj : ∀ u, Φy u = g (χy.symm u) := by
    intro u
    simp only [Φy, χy, writtenInExtChartAt, Function.comp_apply]
    rfl
  have hii : ∀ p, χ p = (χx p.1, χy p.2) := by
    intro p
    simp only [χ, χx, χy, p₀, extChartAt_prod, PartialEquiv.prod_coe]
  -- The coordinate expression of `F` agrees with `F` transported along the product chart.
  have hiv : ∀ p ∈ χ.source, Ψ (χ p) = F p := by
    intro p hp
    have hp12 : p.1 ∈ χx.source ∧ p.2 ∈ χy.source := by
      have h := hp
      simp only [χ, extChartAt_prod, PartialEquiv.prod_source, Set.mem_prod] at h
      exact h
    rw [hii p]
    simp only [Ψ, F]
    rw [hi, hj, χx.left_inv hp12.1, χy.left_inv hp12.2]
  have hp₀W : p₀ ∈ W := by
    refine ⟨?_, ?_⟩
    · simp only [χ]; exact mem_extChartAt_source p₀
    · show χ p₀ ∈ S₀
      rw [hχp₀]
      exact haS₀
  -- Therefore `F` is injective on the neighbourhood `W` of `p₀`.
  have hWinj : ∀ p ∈ W, ∀ q ∈ W, F p = F q → p = q := by
    intro p hp q hq hpq
    have h1 : Ψ (χ p) = Ψ (χ q) := by rw [hiv p hp.1, hiv q hq.1, hpq]
    have h2 : χ p = χ q := hS₀inj (χ p) hp.2 (χ q) hq.2 h1
    rw [← PartialEquiv.left_inv χ hp.1, h2, PartialEquiv.left_inv χ hq.1]
  -- Extract product neighbourhoods of `x₀` and `y₀` inside `W`, and make them disjoint.
  obtain ⟨U', V', hU'open, hV'open, hxU', hyV', hU'V'⟩ :=
    isOpen_prod_iff.mp hWopen x₀ y₀ hp₀W
  obtain ⟨O, O', hOopen, hO'open, hxO, hyO', hdisj⟩ := t2_separation hxy
  refine ⟨U' ∩ O, V' ∩ O', hU'open.inter hOopen, hV'open.inter hO'open,
    ⟨hxU', hxO⟩, ⟨hyV', hyO'⟩, ?_, ?_⟩
  · rw [← Set.subset_empty_iff]
    rintro p ⟨⟨-, hpO⟩, -, hpO'⟩
    exact (Set.disjoint_left.mp hdisj hpO) hpO'
  · intro x hx y hy hgxy
    have hmem : (x, y) ∈ W := hU'V' ⟨hx.1, hy.1⟩
    have hFxy : F (x, y) = F p₀ := by
      simp only [F, p₀, hgxy, h0, sub_self]
    have hpp : (x, y) = p₀ := hWinj (x, y) hmem p₀ hp₀W hFxy
    simp only [p₀, Prod.mk.injEq] at hpp
    exact hpp

end Work.Embedding
