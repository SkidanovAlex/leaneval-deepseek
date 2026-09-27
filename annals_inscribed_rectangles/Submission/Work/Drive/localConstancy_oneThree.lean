import Mathlib
import Submission.Work.Drive.locallyConstant_labelMeet_eq

/-!
# The local solution of a regular family of equations: the analytic core of the count's local constancy

The chain route's side function is a **mod-2 surface count**

> `b u = ⟨#(A_u ⋔ C_0), 1⟩`  (mod 2),  `A_u = P_0 ∩ V_u` the *cut* of the reference plane `P_0` by
> the radial sweep `V_u`, `C_0 ⊂ P_0` the essential loop of `P_0` (a projective line)

(`CUT_TRANSPORT_DESIGN.md` §1).  Both `A_u` and `C_0` are `1`-cycles of the **surface** `P_0 ≅ ℝP²`, so
this is a `1 + 1` count in dimension `2`, *not* a `1 + 3` count in the `4`-manifold `Y` (the
intersection `C_0 ∩ V_u` inside `Y` is genuinely `1`-dimensional and gives no finite count; the design
note of an earlier session that modelled it as a `1+3` meet set is superseded by
`Submission/Work/Drive/localConstancy_surface.lean`).

The analytic content of the local constancy of `u ↦ b u` is nevertheless the same in both pictures and
is what this file provides: the **implicit function theorem for a square family**

> **`Work.Drive.exists_local_solution_of_surjective`** — for a smooth family `G : ℝ → F → E` of maps
> between finite-dimensional real normed spaces *of the same dimension*, `ξ` a zero of `G 0` at which
> the derivative `fderiv ℝ (G 0) ξ` is surjective (hence bijective), there are `ε, δ > 0` and a map
> `ψ` with `ψ 0 = ξ`, continuous at `0`, such that for `|s| < ε` the point `ψ s` is the **unique** zero
> of `G s` in the ball of radius `δ` around `ξ`.

The proof applies the inverse function theorem to `R (s,x) = (s, G s x)`: its derivative at `(0,ξ)` is
the block map `(a,v) ↦ (a, ∂_s G + dG v)`, invertible because `dG = fderiv ℝ (G 0) ξ` is.

The two global ingredients that turn this local statement into the local constancy of a *count* — the
compactness ("every point of the family at `s` is near a point of the family at `0`") and the assembly
(local solutions are disjoint and exhaustive) — are in `localConstancy_surface.lean`.
-/

namespace Work.Drive

open Filter
open scoped Topology ContDiff

noncomputable section

/-- **Transversality of a `1`-chain (a parametrised loop) and a `k`-chain**: the two derivatives
together span the target.  In the surface case (`E` two-dimensional, `k = 1`) this says that the
tangent directions of the two curves at a meeting point are independent. -/
def PairTransverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    [NormedAddCommGroup ι] [NormedSpace ℝ ι] (f : ℝ →L[ℝ] E) (g : ι →L[ℝ] E) : Prop :=
  ∀ w : E, ∃ (a : ℝ) (b : ι), f a - g b = w

/-- **The local solution of a regular family.**  Let `G : ℝ → F → E` be a smooth family of maps
between finite-dimensional real normed spaces of the same dimension, `ξ` a zero of `G 0`, and
`fderiv ℝ (G 0) ξ` surjective — so, the system being square, bijective and hence an isomorphism.
Then near `ξ` the zero set of `G s` is, for `s` near `0`, a *single* point `ψ s`, continuous in `s`.

The proof applies the inverse function theorem to `R (s,x) = (s, G s x)`: its derivative at `(0,ξ)` is
the block map `(a,v) ↦ (a, ∂_s G + dG v)`, invertible because `dG = fderiv ℝ (G 0) ξ` is.  (This is
the counterpart of `Work.Drive.exists_local_solution`, which handles the *boundary* zeros of the
`(m+1) → m` parity set-up using one extra "face" coordinate; here the equation is a square system, so
the device `R (s,x) = (s, G s x)` is already an isomorphism at `(0,ξ)` and no face coordinate is
needed.) -/
theorem exists_local_solution_of_surjective {F E : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : ℝ → F → E)
    (hG : ContDiff ℝ Ctop (fun p : ℝ × F => G p.1 p.2))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {ξ : F} (hξ0 : G 0 ξ = 0)
    (hsurj : Function.Surjective (fderiv ℝ (G 0) ξ)) :
    ∃ (ε δ : ℝ) (ψ : ℝ → F), 0 < ε ∧ 0 < δ ∧ ψ 0 = ξ ∧
      Filter.Tendsto ψ (nhds (0 : ℝ)) (nhds ξ) ∧
      (∀ s, |s| < ε → ‖ψ s - ξ‖ < δ ∧ G s (ψ s) = 0) ∧
      (∀ s, |s| < ε → ∀ x, ‖x - ξ‖ < δ → G s x = 0 → x = ψ s) := by
  classical
  have hne : Ctop ≠ 0 := by decide
  set uG : ℝ × F → E := fun p => G p.1 p.2 with huG
  have hucd : ContDiff ℝ Ctop uG := hG
  have huat : HasFDerivAt uG (fderiv ℝ uG (0, ξ)) (0, ξ) :=
    (hucd.contDiffAt.differentiableAt hne).hasFDerivAt
  set dG : F →L[ℝ] E := fderiv ℝ (G 0) ξ with hdG
  have happ : ∀ w : F, fderiv ℝ uG (0, ξ) (0, w) = dG w := by
    intro w
    have h := congrArg (fun (T : F →L[ℝ] E) => T w) (fderiv_uncurry_snd huat).symm
    simpa [huG, hdG, ContinuousLinearMap.inr_apply] using h
  -- surjective + equal dimensions ⟹ bijective
  have hdGinj : Function.Injective dG :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := dG.toLinearMap) hdim).mpr hsurj
  -- the derivative `L` of `R (s,x) = (s, uG (s,x))`
  set L : ℝ × F →L[ℝ] ℝ × E :=
    (ContinuousLinearMap.fst ℝ ℝ F).prod (fderiv ℝ uG (0, ξ)) with hL
  have hLc : ∀ p : ℝ × F, L p = (p.1, fderiv ℝ uG (0, ξ) p) := fun p => rfl
  have hLsurj : Function.Surjective L := by
    rintro ⟨b, y⟩
    obtain ⟨v, hv⟩ := hsurj (y - b • (fderiv ℝ uG (0, ξ) ((1 : ℝ), (0 : F))))
    refine ⟨(b, v), ?_⟩
    rw [hLc]
    refine Prod.ext rfl ?_
    have hsplit : (b, v) = b • ((1 : ℝ), (0 : F)) + (0, v) := by ext <;> simp
    rw [hsplit, map_add, map_smul, happ, hv]
    abel
  have hdim2 : Module.finrank ℝ (ℝ × F) = Module.finrank ℝ (ℝ × E) := by
    rw [Module.finrank_prod, Module.finrank_prod, hdim]
  have hLinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (L : ℝ × F →ₗ[ℝ] ℝ × E)) hdim2).mpr hLsurj
  have hbij : Function.Bijective (L : ℝ × F →ₗ[ℝ] ℝ × E) := ⟨hLinj, hLsurj⟩
  let e := (LinearEquiv.ofBijective (L : ℝ × F →ₗ[ℝ] ℝ × E) hbij).toContinuousLinearEquiv
  have he : (e : ℝ × F →L[ℝ] ℝ × E) = L := by
    apply ContinuousLinearMap.ext; intro x; rfl
  -- the map `R` and its strict derivative
  set R : ℝ × F → ℝ × E := fun p => (p.1, uG p) with hRdef
  have hRfd : HasFDerivAt R L (0, ξ) := hasFDerivAt_fst.prodMk huat
  have hRcd : ContDiff ℝ Ctop R := by rw [hRdef]; fun_prop
  have hst : HasStrictFDerivAt R (e : ℝ × F →L[ℝ] ℝ × E) (0, ξ) := by
    rw [he, ← hRfd.fderiv]
    exact hRcd.hasStrictFDerivAt hne
  let Φ : OpenPartialHomeomorph (ℝ × F) (ℝ × E) := HasStrictFDerivAt.toOpenPartialHomeomorph R hst
  have hΦcoe : (Φ : ℝ × F → ℝ × E) = R := HasStrictFDerivAt.toOpenPartialHomeomorph_coe hst
  have hsrc : (0, ξ) ∈ Φ.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hst
  have hR0 : R (0, ξ) = ((0 : ℝ), (0 : E)) := by simp [hRdef, huG, hξ0]
  have htgt : R (0, ξ) ∈ Φ.target :=
    HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target hst
  have htgt0 : (((0 : ℝ), (0 : E)) : ℝ × E) ∈ Φ.target := by rwa [← hR0]
  obtain ⟨r_src, hr_src, hr_src'⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hsrc)
  have htgt_nhds : ∀ᶠ s in nhds (0 : ℝ), ((s, (0 : E)) : ℝ × E) ∈ Φ.target :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (Φ.open_target.mem_nhds htgt0)
  obtain ⟨r_tgt, hr_tgt, hr_tgt'⟩ := Metric.mem_nhds_iff.mp htgt_nhds
  have hsymm0 : Φ.symm (((0 : ℝ), (0 : E)) : ℝ × E) = (0, ξ) := by
    have h := Φ.left_inv hsrc
    rw [hΦcoe, hR0] at h
    exact h
  set ψ : ℝ → F := fun s => (Φ.symm ((s, (0 : E)) : ℝ × E)).2 with hψ
  have hψ0 : ψ 0 = ξ := by simp [hψ, hsymm0]
  have hψcont : Filter.Tendsto ψ (nhds (0 : ℝ)) (nhds ξ) := by
    have hs : Filter.Tendsto (fun s : ℝ => Φ.symm ((s, (0 : E)) : ℝ × E)) (nhds (0 : ℝ))
        (nhds (Φ.symm (((0 : ℝ), (0 : E)) : ℝ × E))) :=
      (Φ.continuousAt_symm htgt0).tendsto.comp
        (continuous_id.prodMk continuous_const).continuousAt.tendsto
    rw [hsymm0] at hs
    exact (continuous_snd.continuousAt.tendsto).comp hs
  obtain ⟨r_ψ, hr_ψ, hr_ψ'⟩ := Metric.mem_nhds_iff.mp
    (hψcont.eventually (Metric.ball_mem_nhds ξ hr_src))
  refine ⟨min r_tgt (min r_src r_ψ), r_src, ψ, lt_min hr_tgt (lt_min hr_src hr_ψ), hr_src,
    hψ0, hψcont, ?_, ?_⟩
  · -- existence of the local solution
    intro s hs
    have hs_tgt : |s| < r_tgt := lt_of_lt_of_le hs (min_le_left _ _)
    have hs_ψ : |s| < r_ψ := lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_right _ _))
    have hd_tgt : dist s (0 : ℝ) < r_tgt := by simpa [Real.dist_eq, sub_zero] using hs_tgt
    have hmem_tgt : ((s, (0 : E)) : ℝ × E) ∈ Φ.target := hr_tgt' hd_tgt
    have hRsol : R (Φ.symm ((s, (0 : E)) : ℝ × E)) = ((s, (0 : E)) : ℝ × E) := by
      rw [← hΦcoe]; exact Φ.right_inv hmem_tgt
    have h1 : (Φ.symm ((s, (0 : E)) : ℝ × E)).1 = s := by
      have := congrArg (fun z : ℝ × E => z.1) hRsol
      simpa [hRdef] using this
    have h2 : uG (Φ.symm ((s, (0 : E)) : ℝ × E)) = 0 := by
      have := congrArg (fun z : ℝ × E => z.2) hRsol
      simpa [hRdef] using this
    have hnorm : ‖ψ s - ξ‖ < r_src := by
      have hs_ψ' : dist s (0 : ℝ) < r_ψ := by simpa [Real.dist_eq, sub_zero] using hs_ψ
      have hm := hr_ψ' hs_ψ'
      simpa [Set.mem_ofPred_eq, dist_eq_norm] using hm
    refine ⟨hnorm, ?_⟩
    have hun : G s (ψ s) = uG (Φ.symm ((s, (0 : E)) : ℝ × E)) := by
      simp [huG, hψ, h1]
    rw [hun]; exact h2
  · -- uniqueness of the local solution
    intro s hs x hx hx0
    have hs_src : |s| < r_src :=
      lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_left _ _))
    have hs_src' : dist s (0 : ℝ) < r_src := by simpa [Real.dist_eq, sub_zero] using hs_src
    have hball : ((s, x) : ℝ × F) ∈ Metric.ball ((0, ξ) : ℝ × F) r_src := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hs_src' (by rw [dist_eq_norm]; exact hx)
    have hinsrc : (s, x) ∈ Φ.source := hr_src' hball
    have hΦsx : Φ (s, x) = ((s, (0 : E)) : ℝ × E) := by
      rw [hΦcoe]
      have hRt : R (s, x) = (s, G s x) := by simp [hRdef, huG]
      rw [hRt, hx0]
    have hleft := Φ.left_inv hinsrc
    rw [hΦsx] at hleft
    have hfin : (Φ.symm ((s, (0 : E)) : ℝ × E)).2 = x := by
      have := congrArg (fun z : ℝ × F => z.2) hleft
      simpa using this
    exact hfin.symm

end

end Work.Drive
