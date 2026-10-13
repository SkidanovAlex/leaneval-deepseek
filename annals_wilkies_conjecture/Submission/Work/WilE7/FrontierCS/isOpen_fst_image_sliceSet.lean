/-
  WilE7 / CS-slice, node N6 (inverse function theorem).

  Statement: for `G : ℝ^N → ℝ^j` entire, `W ⊆ {G = 0}` relatively open in `{G = 0}`, `ψ` entire and
  `U` open, the base projection `Prod.fst '' (U ∩ sliceSet G W ψ)` of the slice set cut by `U` is
  open.

  Proof.  Let `p₀ = (τ₀, e₀) ∈ U ∩ sliceSet G W ψ`.  Put `h := G ∘ ψ`, so that the slice condition
  reads `(fderiv ℝ h p₀ ∘L inr).range = ⊤`, i.e. the partial derivative in the second variable is
  surjective; by finite dimensionality it is invertible.  The implicit function theorem
  (`HasStrictFDerivAt.implicitFunctionOfProdDomain`) applied to `h` at `p₀` produces
  `φ : ℝ^d → ℝ^j` with `φ τ₀ = e₀` and `h (τ, φ τ) = 0` for `τ` near `τ₀`.  The locus `Σ` where the
  slice derivative is surjective is open (continuity of the derivative, openness of the invertible
  linear maps), and `ψ ⁻¹' U_w` is a neighbourhood of `p₀` for the relative-openness neighbourhood
  `U_w` of `ψ p₀ ∈ W`.  Hence for all `τ` near `τ₀` the point `(τ, φ τ)` lies in `U`, in `ψ ⁻¹' U_w`
  and in `Σ`; since `G (ψ (τ, φ τ)) = h (τ, φ τ) = 0` and `ψ (τ, φ τ) ∈ U_w`, relative openness gives
  `ψ (τ, φ τ) ∈ W`.  Therefore `(τ, φ τ) ∈ U ∩ sliceSet G W ψ` with `Prod.fst (τ, φ τ) = τ`, so
  `Prod.fst '' (U ∩ sliceSet G W ψ)` is a neighbourhood of `τ₀`.
-/
import Mathlib
import Submission.Work.WilE7.FrontierCS.Defs

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.FrontierCS

/-- A continuous linear self-map of `ℝ^j` whose range is everything is invertible: over the finite
dimensional space `ℝ^j` surjectivity upgrades to bijectivity, whence a continuous linear
equivalence. -/
lemma isInvertible_of_range_top {j : ℕ} (T : (Fin j → ℝ) →L[ℝ] (Fin j → ℝ))
    (hrange : T.range = ⊤) : T.IsInvertible := by
  have hker : T.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact (LinearMap.injective_iff_surjective).mpr (LinearMap.range_eq_top.mp hrange)
  exact ⟨ContinuousLinearEquiv.ofBijective T hker hrange, rfl⟩

/-- For a continuous self-map of `ℝ^j`, having full range is equivalent to being invertible. -/
lemma range_eq_top_iff_isInvertible {j : ℕ} (T : (Fin j → ℝ) →L[ℝ] (Fin j → ℝ)) :
    T.range = ⊤ ↔ T.IsInvertible :=
  ⟨isInvertible_of_range_top T, fun h => LinearMap.range_eq_top.mpr h.surjective⟩

/-- The partial derivative of `h` in the second variable is the full Fréchet derivative of `h`
composed with the inclusion `inr` of the second factor. -/
lemma fderiv_comp_inr {d j : ℕ} {h : (Fin d → ℝ) × (Fin j → ℝ) → (Fin j → ℝ)}
    {p : (Fin d → ℝ) × (Fin j → ℝ)} (hh : HasStrictFDerivAt h (fderiv ℝ h p) p) :
    fderiv ℝ (fun e => h (p.1, e)) p.2 =
      (fderiv ℝ h p) ∘L (ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin j → ℝ)) :=
  (hh.hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).fderiv

/-- **N6 (IFT).** The base projection of the slice set, cut by any open `U`, is open: at a point,
`H (τ,e) = (τ, G (ψ (τ,e)))` has invertible strict derivative, so `H` maps neighbourhoods onto
neighbourhoods of `(τ₀,0)`; level-set points near `ψ p` are in `W` by relative openness. -/
theorem isOpen_fst_image_sliceSet {N d j : ℕ} (hj : 0 < j) {G : (Fin N → ℝ) → (Fin j → ℝ)}
    (hG : AnalyticOnNhd ℝ G Set.univ) {W : Set (Fin N → ℝ)}
    (hWZ : ∀ w ∈ W, G w = 0)
    (hWopen : ∀ w ∈ W, ∃ U ∈ nhds w, ∀ z ∈ U, G z = 0 → z ∈ W)
    {ψ : (Fin d → ℝ) × (Fin j → ℝ) → (Fin N → ℝ)} (hψ : AnalyticOnNhd ℝ ψ Set.univ)
    {U : Set ((Fin d → ℝ) × (Fin j → ℝ))} (hU : IsOpen U) :
    IsOpen (Prod.fst '' (U ∩ Work.WilE7.FrontierCS.sliceSet G W ψ)) := by
  rw [isOpen_iff_mem_nhds]
  intro τ₀ hτ₀
  rw [Set.mem_image] at hτ₀
  obtain ⟨p₀, hp₀, hfst⟩ := hτ₀
  obtain ⟨hpU, hpS⟩ := hp₀
  rw [sliceSet, Set.mem_ofPred_eq] at hpS
  obtain ⟨hψpW, hpjac⟩ := hpS
  have hτ : τ₀ = p₀.1 := hfst.symm
  -- `h = G ∘ ψ` is entire, hence strictly differentiable everywhere.
  have hh_an : AnalyticOnNhd ℝ (G ∘ ψ) Set.univ := hG.comp hψ (fun x _ => Set.mem_univ _)
  have hGψ_sfd : ∀ p, HasStrictFDerivAt (G ∘ ψ) (fderiv ℝ (G ∘ ψ) p) p := fun p =>
    ((hh_an p (Set.mem_univ p)).contDiffAt (n := 1)).hasStrictFDerivAt one_ne_zero
  have hfd_cont : Continuous (fun p : (Fin d → ℝ) × (Fin j → ℝ) => fderiv ℝ (G ∘ ψ) p) :=
    hh_an.fderiv.continuous
  have hcomp_cont : Continuous (fun p : (Fin d → ℝ) × (Fin j → ℝ) =>
      (fderiv ℝ (G ∘ ψ) p) ∘L (ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin j → ℝ))) :=
    hfd_cont.clm_comp_const _
  -- The set where the slice derivative is surjective is open.
  have hSlice_open : IsOpen {p : (Fin d → ℝ) × (Fin j → ℝ) |
      (fderiv ℝ (fun e => G (ψ (p.1, e))) p.2).range = ⊤} := by
    have heq : {p : (Fin d → ℝ) × (Fin j → ℝ) |
          (fderiv ℝ (fun e => G (ψ (p.1, e))) p.2).range = ⊤}
        = {p : (Fin d → ℝ) × (Fin j → ℝ) | ((fderiv ℝ (G ∘ ψ) p) ∘L
            (ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin j → ℝ))).IsInvertible} := by
      ext p
      simp only [Set.mem_ofPred_eq]
      rw [show fderiv ℝ (fun e => G (ψ (p.1, e))) p.2 =
          (fderiv ℝ (G ∘ ψ) p) ∘L
            (ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin j → ℝ)) from by
        simpa only [Function.comp_apply] using
          fderiv_comp_inr (h := G ∘ ψ) (p := p) (hGψ_sfd p)]
      exact range_eq_top_iff_isInvertible _
    rw [heq]
    exact hcomp_cont.isOpen_preimage _ (ContinuousLinearMap.isOpen_setOfPred_isInvertible (𝕜 := ℝ))
  set S0 : Set ((Fin d → ℝ) × (Fin j → ℝ)) :=
    {p | (fderiv ℝ (fun e => G (ψ (p.1, e))) p.2).range = ⊤} with hS0def
  have hS0_open : IsOpen S0 := hSlice_open
  have hp0S0 : p₀ ∈ S0 := by rw [hS0def]; simpa only [Set.mem_ofPred_eq] using hpjac
  -- Surjectivity of the second partial derivative at `p₀` upgrades to invertibility.
  have hpjac_inr : ((fderiv ℝ (G ∘ ψ) p₀) ∘L
      (ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin j → ℝ))).range = ⊤ := by
    rw [← show fderiv ℝ (fun e => G (ψ (p₀.1, e))) p₀.2 =
        (fderiv ℝ (G ∘ ψ) p₀) ∘L
          (ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin j → ℝ)) from by
      simpa only [Function.comp_apply] using
        fderiv_comp_inr (h := G ∘ ψ) (p := p₀) (hGψ_sfd p₀)]
    exact hpjac
  have hIf : ((fderiv ℝ (G ∘ ψ) p₀) ∘L
      (ContinuousLinearMap.inr ℝ (Fin d → ℝ) (Fin j → ℝ))).IsInvertible :=
    (range_eq_top_iff_isInvertible _).mp hpjac_inr
  -- The implicit function `φ` with `h (τ, φ τ) = 0` near `τ₀`.
  let φ : (Fin d → ℝ) → (Fin j → ℝ) := (hGψ_sfd p₀).implicitFunctionOfProdDomain hIf
  have hφ_tendsto : Tendsto φ (𝓝 p₀.1) (𝓝 p₀.2) :=
    (hGψ_sfd p₀).tendsto_implicitFunctionOfProdDomain hIf
  have hφ_apply : ∀ᶠ x in 𝓝 p₀.1, (G ∘ ψ) (x, φ x) = (G ∘ ψ) p₀ :=
    (hGψ_sfd p₀).eventually_apply_implicitFunctionOfProdDomain hIf
  have h0 : (G ∘ ψ) p₀ = 0 := hWZ (ψ p₀) hψpW
  -- Relative openness of `W` at `ψ p₀`.
  obtain ⟨Uw, hUw_mem, hUw_prop⟩ := hWopen (ψ p₀) hψpW
  have hψinv : ψ ⁻¹' Uw ∈ 𝓝 p₀ := hψ.continuous.continuousAt.preimage_mem_nhds hUw_mem
  have hU_mem : U ∈ 𝓝 p₀ := hU.mem_nhds hpU
  have hsU : U ∩ ψ ⁻¹' Uw ∩ S0 ∈ 𝓝 p₀ :=
    Filter.inter_mem (Filter.inter_mem hU_mem hψinv) (hS0_open.mem_nhds hp0S0)
  -- `τ ↦ (τ, φ τ)` is continuous at `τ₀` with value `p₀`.
  have hτφ : Tendsto (fun τ : Fin d → ℝ => (τ, φ τ)) (𝓝 p₀.1) (𝓝 p₀) := by
    rw [show p₀ = (p₀.1, p₀.2) from (Prod.eta p₀).symm, nhds_prod_eq]
    exact tendsto_id.prodMk hφ_tendsto
  have hV1 : (fun τ : Fin d → ℝ => (τ, φ τ)) ⁻¹' (U ∩ ψ ⁻¹' Uw ∩ S0) ∈ 𝓝 p₀.1 :=
    hτφ.eventually hsU
  have hV2 : {τ : Fin d → ℝ | (G ∘ ψ) (τ, φ τ) = 0} ∈ 𝓝 p₀.1 := by
    filter_upwards [hφ_apply] with x hx
    rw [hx, h0]
  rw [hτ]
  refine Filter.mem_of_superset (Filter.inter_mem hV1 hV2) ?_
  rintro τ ⟨hτ1, hτ2⟩
  rw [Set.mem_preimage, Set.mem_inter_iff, Set.mem_inter_iff] at hτ1
  obtain ⟨⟨hτU, hτUw⟩, hτS0⟩ := hτ1
  have hτS0' : (fderiv ℝ (fun e => G (ψ ((τ, φ τ).1, e))) ((τ, φ τ)).2).range = ⊤ := by
    rw [hS0def] at hτS0
    simpa only [Set.mem_ofPred_eq] using hτS0
  exact ⟨(τ, φ τ), ⟨hτU, hUw_prop _ hτUw hτ2, hτS0'⟩, rfl⟩

end Work.WilE7.FrontierCS
