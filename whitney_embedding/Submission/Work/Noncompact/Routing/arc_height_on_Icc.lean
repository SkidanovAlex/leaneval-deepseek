import Mathlib
import Submission.Work.Noncompact.CompressionTube.collar_defs
import Submission.Work.Noncompact.CompressionTube.CollarDefs
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Whitney.exists_sheet_model

/-!
# A height function on a smoothly embedded arc

`Work.Noncompact.Routing.arc_height_on_Icc`: a smooth immersed curve `γ : ℝ → M` in a smooth
`n`-manifold whose restriction to a closed interval `[a,b]` is injective admits a smooth function
`g : M → ℝ` with `g (γ t) = t` for all `t ∈ [a,b]`.

The proof has two completely independent halves.

* **Local half** (`exists_local_left_inverse_on_Icc`).  At a point `s ∈ [a,b]` one chooses a chart
  `c` at `γ s`; the coordinate expression `t ↦ c (γ t)` has injective (hence non-zero) derivative
  at `s`, so some coordinate `u` of it has non-zero derivative.  The inverse function theorem in
  the form `Work.Whitney.exists_localInverse_smooth_on` supplies a local inverse `L` of `u ∘ c ∘ γ`
  near `s`; cutting the chart down and excising the (compact) part of the arc on which the inverse
  is not known to be valid produces an open neighbourhood `U ∋ γ s` and a smooth function
  `F = L ∘ u ∘ c` on it with `F (γ t) = t` for all `t ∈ [a,b]` with `γ t ∈ U`.

* **Gluing half** (`exists_contMDiff_eqOn_of_isCompact_of_local`).  Given a compact set `A`, a
  neighbourhood assignment `U : M → Set M` and functions `F x` smooth on `U x` which agree with a
  prescribed function `φ` on `A ∩ U x`, one produces a globally smooth `g` with `g = φ` on `A`.
  The proof is a finite bump covering of the compact set `A` obtained from
  `SmoothBumpFunction.nhds_basis_support`, together with Mathlib's smooth partition of unity
  attached to a `SmoothBumpCovering`.  It uses no second countability (and no `σ`-compactness) of
  `M`, which the statement of `arc_height_on_Icc` does not assume.

Combining the two on the compact image of `[a,b]` gives the theorem.
-/

namespace Work.Noncompact.Routing

open scoped Manifold ContDiff
open Topology Set Function Filter
open Work.Noncompact.CompressionTube

noncomputable section

/-! ## Gluing local data on a compact set -/

/-- **Gluing local functions on a compact set.**  Let `A` be compact, `U : M → Set M` a family of
open neighbourhoods `U x ∋ x` of the points of `A` and `F x` a function smooth on `U x` which
agrees with `φ` on `A ∩ U x`.  Then there is a smooth `g` on all of `M` with `g = φ` on `A`. -/
theorem exists_contMDiff_eqOn_of_isCompact_of_local {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M]
    {A : Set M} (hA : IsCompact A) {φ : M → ℝ}
    (U : M → Set M) (hUo : ∀ x, IsOpen (U x)) (hUA : ∀ x ∈ A, x ∈ U x)
    (F : M → M → ℝ) (hF : ∀ x, ContMDiffOn (MC n) MCreal smoothOrder (F x) (U x))
    (hUF : ∀ x y, x ∈ A → y ∈ A → y ∈ U x → F x y = φ y) :
    ∃ g : M → ℝ, ContMDiff (MC n) MCreal smoothOrder g ∧ ∀ y ∈ A, g y = φ y := by
  classical
  -- a smooth bump function at each point of `A`, supported in `U x`
  have hbump : ∀ x : M, x ∈ A → ∃ f : SmoothBumpFunction (MC n) x,
      tsupport f ⊆ U x ∧ f =ᶠ[𝓝 x] 1 := by
    intro x hx
    have hmem : U x ∈ 𝓝 x := (hUo x).mem_nhds (hUA x hx)
    obtain ⟨f, hf, -⟩ :=
      (SmoothBumpFunction.nhds_basis_support (I := MC n) hmem).mem_iff.mp hmem
    exact ⟨f, hf, f.eventuallyEq_one⟩
  choose f hfsub hfone using hbump
  have hV : ∀ x (hx : x ∈ A), x ∈ interior {y : M | f x hx y = 1} := by
    intro x hx
    exact mem_interior_iff_mem_nhds.mpr (hfone x hx)
  -- finitely many of the points of `A` already cover `A` by their `1`-sets
  obtain ⟨t, ht⟩ := hA.elim_finite_subcover (fun x : A => interior {y : M | f x.1 x.2 y = 1})
    (fun _ => isOpen_interior) (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, by simpa using hV x hx⟩)
  -- the corresponding smooth bump covering
  let fs : SmoothBumpCovering {i : A // i ∈ t} (MC n) M A :=
    { c := fun i => (i.1 : M)
      toFun := fun i => f (i.1 : M) i.1.2
      c_mem' := fun i => i.1.2
      locallyFinite' := fun _ =>
        ⟨Set.univ, Filter.univ_mem, Set.finite_univ.subset (Set.subset_univ _)⟩
      eventuallyEq_one' := by
        intro x hx
        obtain ⟨i, hit, hxi⟩ := mem_iUnion₂.mp (ht hx)
        exact ⟨⟨i, hit⟩, mem_interior_iff_mem_nhds.mp hxi⟩ }
  have hsub : fs.IsSubordinate U := fun i => hfsub (fs.c i) (fs.c_mem' i)
  -- the associated smooth partition of unity
  let ρ : SmoothPartitionOfUnity {i : A // i ∈ t} (MC n) M A := fs.toSmoothPartitionOfUnity
  have hρ : ρ.IsSubordinate (fun i => U (fs.c i)) := hsub.toSmoothPartitionOfUnity
  refine ⟨fun y => ∑ᶠ i, ρ i y • F (fs.c i) y, ?_, ?_⟩
  · exact hρ.contMDiff_finsum_smul (fun i => hUo (fs.c i)) (fun i => hF (fs.c i))
  · intro y hyA
    have hterm : ∀ i, ρ i y • F (fs.c i) y = ρ i y • φ y := by
      intro i
      by_cases h0 : ρ i y = 0
      · simp [h0]
      · have hmem : y ∈ tsupport (ρ i) := subset_closure (mem_support.mpr h0)
        rw [hUF (fs.c i) y (fs.c_mem' i) hyA (hρ i hmem)]
    change (∑ᶠ i, (ρ i) y • F (fs.c i) y) = φ y
    rw [finsum_congr hterm]
    have h1 : (∑ᶠ i, ρ i y • φ y) = ∑ i ∈ ρ.finsupport y, ρ i y • φ y :=
      (ρ.sum_finsupport_smul_eq_finsum y (fun _ _ => φ y)).symm
    rw [h1, ← Finset.sum_smul, ρ.sum_finsupport y hyA, one_smul]

/-! ## The local left inverse of an immersed arc -/

/-- **Local smooth left inverse of an immersed curve.**  If `γ : ℝ → M` is a smooth immersion and
`γ` is injective on `[a,b]`, then at every point `s ∈ [a,b]` there is an open neighbourhood `U` of
`γ s` carrying a smooth function `F` with `F (γ t) = t` for every `t ∈ [a,b]` with `γ t ∈ U`. -/
theorem exists_local_left_inverse_on_Icc {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (MC n) smoothOrder M] [T2Space M]
    {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    (himm : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t))
    {a b s : ℝ} (hγinj : Set.InjOn γ (Set.Icc a b)) (hs : s ∈ Set.Icc a b) :
    ∃ (U : Set M) (F : M → ℝ), IsOpen U ∧ γ s ∈ U ∧
      ContMDiffOn (MC n) MCreal smoothOrder F U ∧
      ∀ t : ℝ, t ∈ Set.Icc a b → γ t ∈ U → F (γ t) = t := by
  classical
  set c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)) :=
    chartAt (EuclideanSpace ℝ (Fin n)) (γ s) with hc_def
  have hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M :=
    IsManifold.chart_mem_maximalAtlas (γ s)
  have hmem : γ s ∈ c.source := mem_chart_source (EuclideanSpace ℝ (Fin n)) (γ s)
  have hI : IsOpen (γ ⁻¹' c.source) := c.open_source.preimage hγ.continuous
  have hsI : s ∈ γ ⁻¹' c.source := hmem
  have hh_smooth : ContDiffOn ℝ smoothOrder (fun t => c (γ t)) (γ ⁻¹' c.source) :=
    contMDiffOn_iff_contDiffOn.mp
      ((contMDiffOn_of_mem_maximalAtlas hc).comp hγ.contMDiffOn (fun t ht => ht))
  have hh_inj : Function.Injective (fderiv ℝ (fun t => c (γ t)) s) :=
    injective_fderiv_chart_comp hγ hc himm hmem
  have hne : fderiv ℝ (fun t => c (γ t)) s 1 ≠ 0 := fun h0 =>
    one_ne_zero (hh_inj (by rw [h0, map_zero]))
  -- a chart coordinate with non-zero derivative
  obtain ⟨j, hj⟩ : ∃ j : Fin n, (fderiv ℝ (fun t => c (γ t)) s 1) j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hne (PiLp.ext hcon)
  let u : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := EuclideanSpace.proj (𝕜 := ℝ) j
  have hu_apply : ∀ y : EuclideanSpace ℝ (Fin n), u y = y j := fun y => by
    simp [u, PiLp.proj_apply]
  -- the coordinate function and its derivative
  have hG_smooth : ContDiffOn ℝ smoothOrder (fun t => u (c (γ t))) (γ ⁻¹' c.source) :=
    u.contDiff.comp_contDiffOn hh_smooth
  have hG_fderiv : fderiv ℝ (fun t => u (c (γ t))) s =
      u ∘L fderiv ℝ (fun t => c (γ t)) s := by
    have hhat : HasFDerivAt (fun t => c (γ t)) (fderiv ℝ (fun t => c (γ t)) s) s :=
      (hh_smooth.contDiffAt (hI.mem_nhds hsI)).differentiableAt (by simp) |>.hasFDerivAt
    exact (u.hasFDerivAt.comp s hhat).fderiv
  have hG_inj : Function.Injective (fderiv ℝ (fun t => u (c (γ t))) s) := by
    rw [hG_fderiv]
    have hU1 : (u ∘L fderiv ℝ (fun t => c (γ t)) s) 1 ≠ 0 := by
      simpa [hu_apply] using hj
    intro x y hxy
    have h2 : (u ∘L fderiv ℝ (fun t => c (γ t)) s) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have h1 : (x - y) • ((u ∘L fderiv ℝ (fun t => c (γ t)) s) 1) = 0 := by
      calc (x - y) • ((u ∘L fderiv ℝ (fun t => c (γ t)) s) 1)
          = (u ∘L fderiv ℝ (fun t => c (γ t)) s) ((x - y) • (1 : ℝ)) :=
            (ContinuousLinearMap.map_smul _ _ _).symm
        _ = (u ∘L fderiv ℝ (fun t => c (γ t)) s) (x - y) := by rw [smul_eq_mul, mul_one]
        _ = 0 := h2
    rcases smul_eq_zero.mp h1 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hU1
  -- the inverse function theorem
  obtain ⟨L, O, W, hOo, hOs, hWo, hsW, hWV, hLGs, hLsmooth, hLO, hLG, huniq⟩ :=
    Work.Whitney.exists_localInverse_smooth_on (fun t => u (c (γ t))) (γ ⁻¹' c.source) hI s
      hsI hG_smooth hG_inj
  have hGcont : ContinuousAt (fun t => u (c (γ t))) s :=
    (hG_smooth.contDiffAt (hI.mem_nhds hsI)).continuousAt
  obtain ⟨J₁, hJ₁sub, hJ₁open, hsJ₁⟩ :=
    mem_nhds_iff.mp (hGcont.preimage_mem_nhds (hOo.mem_nhds hOs))
  set J : Set ℝ := W ∩ J₁ with hJ_def
  have hJopen : IsOpen J := hWo.inter hJ₁open
  have hsJ : s ∈ J := ⟨hsW, hsJ₁⟩
  -- excise the part of the arc on which the inverse is not known to be valid
  have hKc : IsCompact (Set.Icc a b \ J) := isCompact_Icc.inter_right hJopen.isClosed_compl
  have hγs : γ s ∉ γ '' (Set.Icc a b \ J) := by
    rintro ⟨t, ht, hts⟩
    have ht_eq : t = s := hγinj ht.1 hs hts
    exact ht.2 (ht_eq ▸ hsJ)
  let U : Set M := (γ '' (Set.Icc a b \ J))ᶜ ∩ (c.source ∩ (fun x => u (c x)) ⁻¹' O)
  have hUo : IsOpen U := by
    refine ((hKc.image hγ.continuous).isClosed.isOpen_compl).inter ?_
    exact (u.continuous.comp_continuousOn c.continuousOn).isOpen_inter_preimage c.open_source hOo
  have hγsU : γ s ∈ U := ⟨hγs, hmem, hOs⟩
  refine ⟨U, fun x => L (u (c x)), hUo, hγsU, ?_, ?_⟩
  · have hcU : ContMDiffOn (MC n) (MC n) smoothOrder (c : M → EuclideanSpace ℝ (Fin n)) U :=
      (contMDiffOn_of_mem_maximalAtlas hc).mono (fun x hx => hx.2.1)
    have hucU : ContMDiffOn (MC n) MCreal smoothOrder (fun x => u (c x)) U :=
      u.contMDiff.comp_contMDiffOn hcU
    exact hLsmooth.contMDiffOn.comp hucU (fun x hx => hx.2.2)
  · intro t ht htU
    have htJ : t ∈ J := by
      by_contra htJ'
      exact htU.1 ⟨t, ⟨ht, htJ'⟩, rfl⟩
    have hGtO : u (c (γ t)) ∈ O := hJ₁sub htJ.2
    have hz : t = L (u (c (γ t))) := huniq (u (c (γ t))) hGtO t htJ.1 rfl
    exact hz.symm

/-! ## The height function on the arc -/

theorem arc_height_on_Icc {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M]
    {γ : ℝ → M}
    (hγ : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder γ)
    (himm : ∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) γ t))
    {a b : ℝ} (hab : a ≤ b) (hγinj : Set.InjOn γ (Set.Icc a b)) :
    ∃ g : M → ℝ,
      ContMDiff (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.MCreal
        Work.Noncompact.CompressionTube.smoothOrder g ∧
      ∀ t : ℝ, t ∈ Set.Icc a b → g (γ t) = t := by
  classical
  have _hab := hab
  -- the arc is compact
  have hexA : ∀ y : M, y ∈ (γ '' Set.Icc a b) → ∃ s : ℝ, s ∈ Set.Icc a b ∧ γ s = y := by
    rintro y ⟨s, hs, rfl⟩
    exact ⟨s, hs, rfl⟩
  -- the parameter of a point of the arc
  let p : M → ℝ := fun y => if h : ∃ s : ℝ, s ∈ Set.Icc a b ∧ γ s = y then h.choose else 0
  have hp_mem : ∀ y (h : ∃ s : ℝ, s ∈ Set.Icc a b ∧ γ s = y), p y ∈ Set.Icc a b := by
    intro y h
    have hp : p y = h.choose := dif_pos h
    rw [hp]
    exact h.choose_spec.1
  have hp_val : ∀ y (h : ∃ s : ℝ, s ∈ Set.Icc a b ∧ γ s = y), γ (p y) = y := by
    intro y h
    have hp : p y = h.choose := dif_pos h
    rw [hp]
    exact h.choose_spec.2
  have hpA : ∀ y ∈ (γ '' Set.Icc a b), p y ∈ Set.Icc a b ∧ γ (p y) = y :=
    fun y hy => ⟨hp_mem y (hexA y hy), hp_val y (hexA y hy)⟩
  have hφ : ∀ s : ℝ, s ∈ Set.Icc a b → p (γ s) = s := by
    intro s hs
    have hex : ∃ s' : ℝ, s' ∈ Set.Icc a b ∧ γ s' = γ s := ⟨s, hs, rfl⟩
    exact hγinj (hp_mem (γ s) hex) hs (hp_val (γ s) hex)
  -- local data at every point of the arc
  have hloc : ∀ x : γ '' Set.Icc a b,
      ∃ (U : Set M) (F : M → ℝ), IsOpen U ∧ (x : M) ∈ U ∧
        ContMDiffOn (MC n) MCreal smoothOrder F U ∧
        ∀ y : M, y ∈ (γ '' Set.Icc a b) → y ∈ U → F y = p y := by
    intro x
    obtain ⟨hxK, hxv⟩ := hpA (x : M) x.2
    obtain ⟨U, F, hUo, hxU, hFs, hUF⟩ := exists_local_left_inverse_on_Icc hγ himm hγinj hxK
    refine ⟨U, F, hUo, ?_, hFs, ?_⟩
    · rw [← hxv]
      exact hxU
    · intro y hyA hyU
      obtain ⟨hyK, hyv⟩ := hpA y hyA
      have h1 : F (γ (p y)) = p y := hUF (p y) hyK (by rw [hyv]; exact hyU)
      rwa [hyv] at h1
  choose Uloc Floc hUloc_o hUloc_x hUloc_sm hUloc_prop using hloc
  -- extend the local data from the arc to all of `M`
  let U' : M → Set M := fun x => if h : x ∈ (γ '' Set.Icc a b) then Uloc ⟨x, h⟩ else Set.univ
  let F' : M → M → ℝ := fun x => if h : x ∈ (γ '' Set.Icc a b) then Floc ⟨x, h⟩ else 0
  have hU'o : ∀ x, IsOpen (U' x) := by
    intro x
    by_cases h : x ∈ (γ '' Set.Icc a b)
    · have hx : U' x = Uloc ⟨x, h⟩ := dif_pos h
      rw [hx]
      exact hUloc_o ⟨x, h⟩
    · have hx : U' x = Set.univ := dif_neg h
      rw [hx]
      exact isOpen_univ
  have hU'A : ∀ x ∈ (γ '' Set.Icc a b), x ∈ U' x := by
    intro x hx
    have h : U' x = Uloc ⟨x, hx⟩ := dif_pos hx
    rw [h]
    exact hUloc_x ⟨x, hx⟩
  have hF'md : ∀ x, ContMDiffOn (MC n) MCreal smoothOrder (F' x) (U' x) := by
    intro x
    by_cases h : x ∈ (γ '' Set.Icc a b)
    · have h1 : F' x = Floc ⟨x, h⟩ := dif_pos h
      have h2 : U' x = Uloc ⟨x, h⟩ := dif_pos h
      rw [h1, h2]
      exact hUloc_sm ⟨x, h⟩
    · have h1 : F' x = 0 := dif_neg h
      have h2 : U' x = Set.univ := dif_neg h
      rw [h1, h2]
      exact contMDiffOn_const
  have hUF' : ∀ x y, x ∈ (γ '' Set.Icc a b) → y ∈ (γ '' Set.Icc a b) → y ∈ U' x →
      F' x y = p y := by
    intro x y hxA hyA hyU
    have h1 : F' x = Floc ⟨x, hxA⟩ := dif_pos hxA
    have h2 : U' x = Uloc ⟨x, hxA⟩ := dif_pos hxA
    rw [h1]
    exact hUloc_prop ⟨x, hxA⟩ y hyA (by rwa [h2] at hyU)
  obtain ⟨g, hg_sm, hg_val⟩ :=
    exists_contMDiff_eqOn_of_isCompact_of_local (isCompact_Icc.image hγ.continuous) U' hU'o
      hU'A F' hF'md hUF'
  exact ⟨g, hg_sm, fun t ht => by
    have h1 : g (γ t) = p (γ t) := hg_val (γ t) ⟨t, ht, rfl⟩
    rwa [hφ t ht] at h1⟩

end

end Work.Noncompact.Routing
