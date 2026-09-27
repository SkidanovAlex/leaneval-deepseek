import Mathlib
import Submission.Work.Drive.meetBoxEngine
import Submission.Work.Drive.localConstancy_oneThree

namespace Work.Drive

open Filter
open scoped Topology ContDiff

noncomputable section

/-!
# The loop-vs-`3`-chain counting engine with a general family parameter

`Submission/Work/Drive/meetBoxEngine.lean` proves the local constancy of the loop-vs-chain meet count
for a **one-parameter** (`ℝ`-parametrised) family `s ↦ (L, D s)` in which the loop `L` is fixed.  The
germ route of `Work.Drive.sideGerm` perturbs *both* the loop's chart and the sweep's chart
independently, so the parameter space is a product `𝔼^m × 𝔼^m` and the loop moves with it; the
one-parameter form gives constancy only along each ray, with radii not bounded below over the
directions.

This file lifts the whole engine — the implicit function theorem for the square family, the
compactness cover of the box, and the assembly — to a parameter space `P` that is an arbitrary
finite-dimensional real normed space.  The mathematics is unchanged: the IFT at each base meet of the
square system `(s, x) ↦ L s x.1 - D s x.2`, plus the compactness cover of the box, and only the
*upper* semicontinuity direction uses the compactness (of the box, a product of `ℝ`-compacts), so it
is dimension-independent. -/

/-- **The partial derivative of an uncurried family** (general parameter space): if `f : P × F → G`
has derivative `f'` at `(t₀,x₀)`, then the derivative of the partial map `y ↦ f (t₀, y)` at `x₀` is
`f'` composed with the inclusion of the second factor. -/
lemma fderiv_uncurry_snd_par {P F G : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : P × F → G} {f' : P × F →L[ℝ] G} {t₀ : P} {x₀ : F}
    (hf : HasFDerivAt f f' (t₀, x₀)) :
    fderiv ℝ (fun y : F => f (t₀, y)) x₀ = f' ∘L ContinuousLinearMap.inr ℝ P F := by
  have h : HasFDerivAt (fun y : F => (t₀, y)) (ContinuousLinearMap.inr ℝ P F) x₀ :=
    hasFDerivAt_prodMk_right t₀ x₀
  exact (hf.comp x₀ h).fderiv

/-- **The local solution of a regular family, with a general parameter space.**  Let
`G : P → F → E` be a smooth family of maps between finite-dimensional real normed spaces (`P` the
family parameter, `F` and `E` of the same dimension), `ξ` a zero of `G 0` at which the derivative
`fderiv ℝ (G 0) ξ` is surjective — so, the system being square, bijective and hence an isomorphism.
Then near `ξ` the zero set of `G s` is, for `s` near `0`, a *single* point `ψ s`, continuous in `s`.

The proof applies the inverse function theorem to `R (s,x) = (s, G s x)`: its derivative at `(0,ξ)` is
the block map `(a,v) ↦ (a, ∂_s G + dG v)`, invertible because `dG = fderiv ℝ (G 0) ξ` is.  This is
`Work.Drive.exists_local_solution_of_surjective` with `ℝ` replaced by the general parameter space. -/
theorem exists_local_solution_of_surjective_par {P F E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (G : P → F → E)
    (hG : ContDiff ℝ Ctop (fun p : P × F => G p.1 p.2))
    (hdim : Module.finrank ℝ F = Module.finrank ℝ E)
    {ξ : F} (hξ0 : G 0 ξ = 0)
    (hsurj : Function.Surjective (fderiv ℝ (G 0) ξ)) :
    ∃ (ε δ : ℝ) (ψ : P → F), 0 < ε ∧ 0 < δ ∧ ψ 0 = ξ ∧
      Filter.Tendsto ψ (nhds (0 : P)) (nhds ξ) ∧
      (∀ s, ‖s‖ < ε → ‖ψ s - ξ‖ < δ ∧ G s (ψ s) = 0) ∧
      (∀ s, ‖s‖ < ε → ∀ x, ‖x - ξ‖ < δ → G s x = 0 → x = ψ s) := by
  classical
  have hne : Ctop ≠ 0 := by decide
  set uG : P × F → E := fun p => G p.1 p.2 with huG
  have hucd : ContDiff ℝ Ctop uG := hG
  have huat : HasFDerivAt uG (fderiv ℝ uG (0, ξ)) (0, ξ) :=
    (hucd.contDiffAt.differentiableAt hne).hasFDerivAt
  set dG : F →L[ℝ] E := fderiv ℝ (G 0) ξ with hdG
  have happ : ∀ w : F, fderiv ℝ uG (0, ξ) (0, w) = dG w := by
    intro w
    have h := congrArg (fun (T : F →L[ℝ] E) => T w) (fderiv_uncurry_snd_par huat).symm
    simpa [huG, hdG, ContinuousLinearMap.inr_apply] using h
  -- surjective + equal dimensions ⟹ bijective
  have hdGinj : Function.Injective dG :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := dG.toLinearMap) hdim).mpr hsurj
  -- the derivative `L` of `R (s,x) = (s, uG (s,x))`
  set L : P × F →L[ℝ] P × E :=
    (ContinuousLinearMap.fst ℝ P F).prod (fderiv ℝ uG (0, ξ)) with hL
  have hLc : ∀ p : P × F, L p = (p.1, fderiv ℝ uG (0, ξ) p) := fun p => rfl
  have hLsurj : Function.Surjective L := by
    rintro ⟨b, y⟩
    obtain ⟨v, hv⟩ := hsurj (y - fderiv ℝ uG (0, ξ) (b, (0 : F)))
    refine ⟨(b, v), ?_⟩
    rw [hLc]
    refine Prod.ext rfl ?_
    have hsplit : (b, v) = (b, (0 : F)) + (0, v) := by ext <;> simp
    rw [hsplit, map_add, happ, hv]
    abel
  have hdim2 : Module.finrank ℝ (P × F) = Module.finrank ℝ (P × E) := by
    rw [Module.finrank_prod, Module.finrank_prod, hdim]
  have hLinj : Function.Injective L :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := (L : P × F →ₗ[ℝ] P × E)) hdim2).mpr hLsurj
  have hbij : Function.Bijective (L : P × F →ₗ[ℝ] P × E) := ⟨hLinj, hLsurj⟩
  let e := (LinearEquiv.ofBijective (L : P × F →ₗ[ℝ] P × E) hbij).toContinuousLinearEquiv
  have he : (e : P × F →L[ℝ] P × E) = L := by
    apply ContinuousLinearMap.ext; intro x; rfl
  -- the map `R` and its strict derivative
  set R : P × F → P × E := fun p => (p.1, uG p) with hRdef
  have hRfd : HasFDerivAt R L (0, ξ) := hasFDerivAt_fst.prodMk huat
  have hRcd : ContDiff ℝ Ctop R := by rw [hRdef]; fun_prop
  have hst : HasStrictFDerivAt R (e : P × F →L[ℝ] P × E) (0, ξ) := by
    rw [he, ← hRfd.fderiv]
    exact hRcd.hasStrictFDerivAt hne
  let Φ : OpenPartialHomeomorph (P × F) (P × E) := HasStrictFDerivAt.toOpenPartialHomeomorph R hst
  have hΦcoe : (Φ : P × F → P × E) = R := HasStrictFDerivAt.toOpenPartialHomeomorph_coe hst
  have hsrc : (0, ξ) ∈ Φ.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hst
  have hR0 : R (0, ξ) = ((0 : P), (0 : E)) := by simp [hRdef, huG, hξ0]
  have htgt : R (0, ξ) ∈ Φ.target :=
    HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target hst
  have htgt0 : (((0 : P), (0 : E)) : P × E) ∈ Φ.target := by rwa [← hR0]
  obtain ⟨r_src, hr_src, hr_src'⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hsrc)
  have htgt_nhds : ∀ᶠ s in nhds (0 : P), ((s, (0 : E)) : P × E) ∈ Φ.target :=
    (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds
      (Φ.open_target.mem_nhds htgt0)
  obtain ⟨r_tgt, hr_tgt, hr_tgt'⟩ := Metric.mem_nhds_iff.mp htgt_nhds
  have hsymm0 : Φ.symm (((0 : P), (0 : E)) : P × E) = (0, ξ) := by
    have h := Φ.left_inv hsrc
    rw [hΦcoe, hR0] at h
    exact h
  set ψ : P → F := fun s => (Φ.symm ((s, (0 : E)) : P × E)).2 with hψ
  have hψ0 : ψ 0 = ξ := by simp [hψ, hsymm0]
  have hψcont : Filter.Tendsto ψ (nhds (0 : P)) (nhds ξ) := by
    have hs : Filter.Tendsto (fun s : P => Φ.symm ((s, (0 : E)) : P × E)) (nhds (0 : P))
        (nhds (Φ.symm (((0 : P), (0 : E)) : P × E))) :=
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
    have hs_tgt : ‖s‖ < r_tgt := lt_of_lt_of_le hs (min_le_left _ _)
    have hs_ψ : ‖s‖ < r_ψ := lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_right _ _))
    have hd_tgt : dist s (0 : P) < r_tgt := by simpa [dist_eq_norm, sub_zero] using hs_tgt
    have hmem_tgt : ((s, (0 : E)) : P × E) ∈ Φ.target := hr_tgt' hd_tgt
    have hRsol : R (Φ.symm ((s, (0 : E)) : P × E)) = ((s, (0 : E)) : P × E) := by
      rw [← hΦcoe]; exact Φ.right_inv hmem_tgt
    have h1 : (Φ.symm ((s, (0 : E)) : P × E)).1 = s := by
      have := congrArg (fun z : P × E => z.1) hRsol
      simpa [hRdef] using this
    have h2 : uG (Φ.symm ((s, (0 : E)) : P × E)) = 0 := by
      have := congrArg (fun z : P × E => z.2) hRsol
      simpa [hRdef] using this
    have hnorm : ‖ψ s - ξ‖ < r_src := by
      have hs_ψ' : dist s (0 : P) < r_ψ := by simpa [dist_eq_norm, sub_zero] using hs_ψ
      have hm := hr_ψ' hs_ψ'
      simpa [Set.mem_ofPred_eq, dist_eq_norm] using hm
    refine ⟨hnorm, ?_⟩
    have hun : G s (ψ s) = uG (Φ.symm ((s, (0 : E)) : P × E)) := by
      simp [huG, hψ, h1]
    rw [hun]; exact h2
  · -- uniqueness of the local solution
    intro s hs x hx hx0
    have hs_src : ‖s‖ < r_src :=
      lt_of_lt_of_le hs (le_trans (min_le_right _ _) (min_le_left _ _))
    have hs_src' : dist s (0 : P) < r_src := by simpa [dist_eq_norm, sub_zero] using hs_src
    have hball : ((s, x) : P × F) ∈ Metric.ball ((0, ξ) : P × F) r_src := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hs_src' (by rw [dist_eq_norm]; exact hx)
    have hinsrc : (s, x) ∈ Φ.source := hr_src' hball
    have hΦsx : Φ (s, x) = ((s, (0 : E)) : P × E) := by
      rw [hΦcoe]
      have hRt : R (s, x) = (s, G s x) := by simp [hRdef, huG]
      rw [hRt, hx0]
    have hleft := Φ.left_inv hinsrc
    rw [hΦsx] at hleft
    have hfin : (Φ.symm ((s, (0 : E)) : P × E)).2 = x := by
      have := congrArg (fun z : P × F => z.2) hleft
      simpa using this
    exact hfin.symm

/-- **Upper semicontinuity of the loop-vs-chain meet set, with a general family parameter.**  With the
*closed* box, for `s → 0` every meet point of the family at `s` is close to a meet point of the family
at `0`; the interiority hypothesis rules out the box boundary.  This is
`Work.Drive.eventually_meetBox_cover` with `ℝ` replaced by the general parameter space `P`; the
compactness used is that of the *box*, not of the parameter space. -/
theorem eventually_meetBox_cover_par {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : P → ℝ → E} {D : P → EuclideanSpace ℝ (Fin 3) → E}
    (hcont : Continuous (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => L q.1 q.2.1 - D q.1 q.2.2))
    (hint : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p.1 ∈ Set.Icc (0 : ℝ) 1 →
      p.2 ∈ Submission.Drive.unitBox 2 → L 0 p.1 = D 0 p.2 →
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1)
    {δ : meetBox (L 0) (D 0) → ℝ} (hδ : ∀ ξ, 0 < δ ξ) :
    ∀ᶠ s in nhds (0 : P), ∀ p ∈ meetBox (L s) (D s),
      ∃ ξ : meetBox (L 0) (D 0), ‖p - ξ.1‖ < δ ξ := by
  have key : ∃ ε > 0, ∀ s, ‖s‖ < ε → ∀ p ∈ meetBox (L s) (D s),
      ∃ ξ : meetBox (L 0) (D 0), ‖p - ξ.1‖ < δ ξ := by
    by_contra hcon
    push Not at hcon
    have hseq : ∀ k : ℕ, ∃ s : P, ∃ p : ℝ × EuclideanSpace ℝ (Fin 3),
        ‖s‖ < 1 / ((k : ℝ) + 1) ∧ p ∈ meetBox (L s) (D s) ∧
        ∀ ξ : meetBox (L 0) (D 0), δ ξ ≤ ‖p - ξ.1‖ := by
      intro k
      obtain ⟨s, hs, p, hp, hfar⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
      exact ⟨s, p, hs, hp, hfar⟩
    choose s p hs hp hfar using hseq
    have hst : Tendsto s atTop (nhds (0 : P)) := by
      refine squeeze_zero_norm' (a := fun k : ℕ => 1 / ((k : ℝ) + 1)) ?_
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact Eventually.of_forall fun k => le_of_lt (hs k)
    have hpm : ∀ k, p k ∈ Set.Icc (0 : ℝ) 1 ×ˢ Submission.Drive.unitBox 2 := fun k => by
      obtain ⟨ht, hv, -⟩ := mem_meetBox.mp (hp k)
      exact ⟨ht, hv⟩
    obtain ⟨a, ha, φ, hφ, hpt⟩ :=
      (isCompact_Icc.prod (isCompact_unitBox 2)).tendsto_subseq hpm
    have hpair : Tendsto (fun k : ℕ => (s (φ k), p (φ k))) atTop (nhds ((0 : P), a)) :=
      (hst.comp hφ.tendsto_atTop).prodMk_nhds hpt
    have hzero : L 0 a.1 - D 0 a.2 = 0 := by
      have h1 : Tendsto (fun k : ℕ => L (s (φ k)) (p (φ k)).1 - D (s (φ k)) (p (φ k)).2) atTop
          (nhds (L 0 a.1 - D 0 a.2)) :=
        (hcont.continuousAt (x := ((0 : P), a))).tendsto.comp hpair
      have h2 : Tendsto (fun k : ℕ => L (s (φ k)) (p (φ k)).1 - D (s (φ k)) (p (φ k)).2) atTop
          (nhds (0 : E)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards with k
        exact (sub_eq_zero.mpr (mem_meetBox.mp (hp (φ k))).2.2).symm
      exact tendsto_nhds_unique h1 h2
    have hLa : L 0 a.1 = D 0 a.2 := sub_eq_zero.mp hzero
    have hamem : a ∈ meetBox (L 0) (D 0) := ⟨ha.1, ha.2, hLa⟩
    have hfar' : ∀ k, δ ⟨a, hamem⟩ ≤ ‖p (φ k) - a‖ := fun k => by
      simpa using hfar (φ k) ⟨a, hamem⟩
    have hev : ∀ᶠ k in atTop, ‖p (φ k) - a‖ < δ ⟨a, hamem⟩ :=
      hpt.eventually (Metric.ball_mem_nhds a (hδ ⟨a, hamem⟩))
    obtain ⟨k, hk⟩ := hev.exists
    exact absurd hk (not_lt.mpr (hfar' k))
  obtain ⟨ε, hε, hval⟩ := key
  filter_upwards [Metric.ball_mem_nhds (0 : P) hε] with s hs
  refine hval s ?_
  have : dist s 0 < ε := by simpa [Metric.mem_ball] using hs
  rwa [dist_eq_norm, sub_zero] at this

/-- **The loop-vs-`3`-chain engine with a general family parameter: local constancy of the number of
meets.**  Both the loop `L s` (`1` parameter) and the chain `D s` (three parameters) move with the
family parameter `s ∈ P`; the difference map `(s,q) ↦ L s q.1 − D s q.2` is smooth, the meet set at
`s = 0` is finite, every base meet is *interior* in the box and *regular* (the derivative of the
difference map is surjective; the box and the target having the same dimension, this is
transversality).  Then the number of meet points is constant for `s` near `0`.

This is `Work.Drive.eventually_ncard_meetBox_eq` with `ℝ` replaced by `P`; the two ingredients are the
general-parameter IFT `exists_local_solution_of_surjective_par` and the cover
`eventually_meetBox_cover_par`. -/
theorem eventually_ncard_meetBox_eq_par {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : P → ℝ → E) (D : P → EuclideanSpace ℝ (Fin 3) → E)
    (hL : ContDiff ℝ Ctop (fun q : P × ℝ => L q.1 q.2))
    (hD : ContDiff ℝ Ctop (fun q : P × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (hfin : (meetBox (L 0) (D 0)).Finite)
    (hint : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p.1 ∈ Set.Icc (0 : ℝ) 1 →
      p.2 ∈ Submission.Drive.unitBox 2 → L 0 p.1 = D 0 p.2 →
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1)
    (hdim : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 3)) = Module.finrank ℝ E)
    (hreg : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p.1 ∈ Set.Icc (0 : ℝ) 1 →
      p.2 ∈ Submission.Drive.unitBox 2 → L 0 p.1 = D 0 p.2 →
      Function.Surjective
        (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => L 0 q.1 - D 0 q.2) p)) :
    ∀ᶠ s in nhds (0 : P),
      (meetBox (L s) (D s)).ncard = (meetBox (L 0) (D 0)).ncard := by
  classical
  have hG : ContDiff ℝ Ctop
      (fun q : P × (ℝ × EuclideanSpace ℝ (Fin 3)) => L q.1 q.2.1 - D q.1 q.2.2) := by fun_prop
  haveI : Finite (meetBox (L 0) (D 0)) := hfin.to_subtype
  haveI : Fintype (meetBox (L 0) (D 0)) := hfin.fintype
  -- local solutions at each meet of the base chain
  have hloc : ∀ ξ : meetBox (L 0) (D 0), ∃ (ε δ : ℝ) (ψ : P → ℝ × EuclideanSpace ℝ (Fin 3)),
      0 < ε ∧ 0 < δ ∧ ψ 0 = ξ.1 ∧ Tendsto ψ (nhds (0 : P)) (nhds ξ.1) ∧
      (∀ s, ‖s‖ < ε → ‖ψ s - ξ.1‖ < δ ∧ L s (ψ s).1 - D s (ψ s).2 = 0) ∧
      (∀ s, ‖s‖ < ε → ∀ x, ‖x - ξ.1‖ < δ → L s x.1 - D s x.2 = 0 → x = ψ s) := by
    intro ξ
    have hξ0 : (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => L 0 q.1 - D 0 q.2) ξ.1 = 0 :=
      sub_eq_zero.mpr ξ.2.2.2
    exact exists_local_solution_of_surjective_par (fun s q => L s q.1 - D s q.2) hG hdim hξ0
      (hreg ξ.1 ξ.2.1 ξ.2.2.1 ξ.2.2.2)
  choose ε₀ δ₀ ψ₀ hε₀ hδ₀ hψ₀ hcont₀ hmain₀ huniq₀ using hloc
  obtain ⟨ρ, hρpos, hρ⟩ := exists_pos_le_dist_of_finite hfin
  -- a radius inside the *open* box at each meet point
  have hff : ∀ ξ : meetBox (L 0) (D 0), ∃ r : ℝ, 0 < r ∧
      ∀ x : ℝ × EuclideanSpace ℝ (Fin 3), ‖x - ξ.1‖ < r →
        x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ∈ Submission.Drive.unitBox 2 :=
    fun ξ => exists_box_radius ξ.1 (hint ξ.1 ξ.2.1 ξ.2.2.1 ξ.2.2.2).1
      (hint ξ.1 ξ.2.1 ξ.2.2.1 ξ.2.2.2).2
  choose rf hrfpos hrf using hff
  set δZ : meetBox (L 0) (D 0) → ℝ := fun ξ => min (δ₀ ξ) (min (rf ξ) ρ) with hδZdef
  have hδZval : ∀ ξ, δZ ξ = min (δ₀ ξ) (min (rf ξ) ρ) := fun ξ => rfl
  have hδZpos : ∀ ξ, 0 < δZ ξ := by
    intro ξ; rw [hδZval]; exact lt_min (hδ₀ ξ) (lt_min (hrfpos ξ) hρpos)
  have hδZ_le_δ₀ : ∀ ξ, δZ ξ ≤ δ₀ ξ := fun ξ =>
    (le_of_eq (hδZval ξ)).trans (min_le_left _ _)
  have hδZ_le_rf : ∀ ξ, δZ ξ ≤ rf ξ := fun ξ =>
    (le_of_eq (hδZval ξ)).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδZ_le_ρ : ∀ ξ, δZ ξ ≤ ρ := fun ξ =>
    (le_of_eq (hδZval ξ)).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hevA : ∀ᶠ s in nhds (0 : P), ∀ ξ : meetBox (L 0) (D 0),
      ‖ψ₀ ξ s - ξ.1‖ < δZ ξ ∧ L s (ψ₀ ξ s).1 - D s (ψ₀ ξ s).2 = 0 := by
    rw [Filter.eventually_all]
    intro ξ
    have h1 : ∀ᶠ s in nhds (0 : P), ‖s‖ < ε₀ ξ := by
      filter_upwards [Metric.ball_mem_nhds (0 : P) (hε₀ ξ)] with s hs
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hs
      exact hs
    have h2 : ∀ᶠ s in nhds (0 : P), ‖ψ₀ ξ s - ξ.1‖ < δZ ξ := by
      have hc := (hcont₀ ξ).eventually (Metric.ball_mem_nhds ξ.1 (hδZpos ξ))
      filter_upwards [hc] with s hs
      simpa [dist_eq_norm] using hs
    filter_upwards [h1, h2] with s hs1 hs2
    exact ⟨hs2, (hmain₀ ξ s hs1).2⟩
  have hevB : ∀ᶠ s in nhds (0 : P), ∀ p ∈ meetBox (L s) (D s),
      ∃ ξ : meetBox (L 0) (D 0), ‖p - ξ.1‖ < δZ ξ :=
    eventually_meetBox_cover_par hG.continuous hint hδZpos
  have hevC : ∀ᶠ s in nhds (0 : P), ∀ ξ : meetBox (L 0) (D 0),
      ∀ x : ℝ × EuclideanSpace ℝ (Fin 3), ‖x - ξ.1‖ < δZ ξ →
      L s x.1 - D s x.2 = 0 → x = ψ₀ ξ s := by
    rw [Filter.eventually_all]
    intro ξ
    have h1 : ∀ᶠ s in nhds (0 : P), ‖s‖ < ε₀ ξ := by
      filter_upwards [Metric.ball_mem_nhds (0 : P) (hε₀ ξ)] with s hs
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hs
      exact hs
    filter_upwards [h1] with s hs1 x hx hx0
    exact huniq₀ ξ s hs1 x (lt_of_lt_of_le hx (hδZ_le_δ₀ ξ)) hx0
  filter_upwards [hevA, hevB, hevC] with s hA hB hC
  set Ψ : meetBox (L 0) (D 0) → ℝ × EuclideanSpace ℝ (Fin 3) := fun ξ => ψ₀ ξ s with hΨdef
  have hΨval : ∀ ξ : meetBox (L 0) (D 0), Ψ ξ = ψ₀ ξ s := fun ξ => rfl
  have hΨmem : ∀ ξ : meetBox (L 0) (D 0), Ψ ξ ∈ meetBox (L s) (D s) := by
    intro ξ
    have hfr := hrf ξ (Ψ ξ) (lt_of_lt_of_le (hA ξ).1 (hδZ_le_rf ξ))
    exact ⟨hfr.1, hfr.2, sub_eq_zero.mp (hA ξ).2⟩
  have hΨinj : Function.Injective Ψ := by
    intro ξ η hξη
    by_contra hne
    have hd : ξ.1 ≠ η.1 := fun h => hne (Subtype.ext h)
    have h1 : ‖Ψ ξ - ξ.1‖ < δZ ξ := (hA ξ).1
    have h2 : ‖Ψ η - η.1‖ < δZ η := (hA η).1
    have h3 : 2 * ρ ≤ ‖ξ.1 - η.1‖ := hρ ξ.1 ξ.2 η.1 η.2 hd
    have h4 : ‖ξ.1 - η.1‖ ≤ ‖Ψ ξ - ξ.1‖ + ‖Ψ η - η.1‖ := by
      have hsub : ξ.1 - η.1 = (ξ.1 - Ψ ξ) + (Ψ ξ - η.1) := by abel
      calc ‖ξ.1 - η.1‖ = ‖(ξ.1 - Ψ ξ) + (Ψ ξ - η.1)‖ := by rw [hsub]
        _ ≤ ‖ξ.1 - Ψ ξ‖ + ‖Ψ ξ - η.1‖ := norm_add_le _ _
        _ = ‖Ψ ξ - ξ.1‖ + ‖Ψ η - η.1‖ := by rw [norm_sub_rev, hξη]
    have h5 : δZ ξ + δZ η ≤ 2 * ρ := by linarith [hδZ_le_ρ ξ, hδZ_le_ρ η]
    linarith
  have hΨsurj : ∀ x ∈ meetBox (L s) (D s), ∃ ξ : meetBox (L 0) (D 0), Ψ ξ = x := by
    intro x hx
    obtain ⟨ξ, hdist⟩ := hB x hx
    refine ⟨ξ, ?_⟩
    rw [hΨval ξ]
    exact (hC ξ x hdist (sub_eq_zero.mpr hx.2.2)).symm
  let Φ : meetBox (L 0) (D 0) → meetBox (L s) (D s) := fun ξ => ⟨Ψ ξ, hΨmem ξ⟩
  have hΦinj : Function.Injective Φ := by
    intro ξ η h
    exact hΨinj (congrArg Subtype.val h)
  have hΦsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨ξ, hξ⟩ := hΨsurj x.1 x.2
    exact ⟨ξ, Subtype.ext hξ⟩
  have hcard : Nat.card (meetBox (L s) (D s)) = Nat.card (meetBox (L 0) (D 0)) :=
    Nat.card_congr (Equiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩).symm
  have hfinS : Finite (meetBox (L s) (D s)) := Finite.of_surjective Φ hΦsurj
  have hfS : (meetBox (L s) (D s)).Finite := Set.finite_coe_iff.mp hfinS
  haveI : Fintype (meetBox (L s) (D s)) := hfS.fintype
  have hA' : (meetBox (L s) (D s)).ncard = Nat.card (meetBox (L s) (D s)) := by
    rw [Set.ncard_eq_toFinset_card _ hfS, hfS.card_toFinset, Fintype.card_eq_nat_card]
  have hB' : (meetBox (L 0) (D 0)).ncard = Nat.card (meetBox (L 0) (D 0)) := by
    rw [Set.ncard_eq_toFinset_card _ hfin, hfin.card_toFinset, Fintype.card_eq_nat_card]
  exact hA'.trans (hcard.trans hB'.symm)

/-- The loop-vs-3-chain counting engine with a family parameter in `EuclideanSpace ℝ (Fin N)`, in
which **both** the loop and the chain vary with the parameter (a generalisation of the proved
`Work.Drive.eventually_ncard_meetBox_eq`, whose family parameter is `ℝ` and whose loop is fixed).

This is needed by the germ route of `Work.Drive.sideGerm`: the perturbation family of the count is
`t ↦ (Ξ t.1 ∘ Q, Ξ t.2 ∘ Q)` — two *independent* chart perturbations, of the loop's chart and of the
sweep's chart — so the parameter space is `𝔼^m × 𝔼^m` and the loop moves with it.  The one-parameter
form gives constancy only along each ray, with radii not bounded below over the directions, which is not
enough.

The proof is the one of `Work.Drive.eventually_ncard_meetBox_eq`: the IFT at each base meet of the
square system `(s, x) ↦ L s x.1 - D s x.2` (with `s` in a finite-dimensional space; the two
ℝ-parametrised auxiliaries `Work.Drive.exists_local_solution_of_surjective` and
`Work.Drive.every_eventually_placeholder` have to be lifted to the general parameter, which is
mechanical), plus the compactness cover of the box; only the *upper* semicontinuity direction needs the
compactness, and it is dimension-independent. -/
theorem eventually_ncard_meetBox_eq_fam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ}
    (L : EuclideanSpace ℝ (Fin N) → ℝ → E)
    (D : EuclideanSpace ℝ (Fin N) → EuclideanSpace ℝ (Fin 3) → E)
    (hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin N) × ℝ => L q.1 q.2))
    (hD : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (hfin : (Work.Drive.meetBox (L 0) (D 0)).Finite)
    (hint : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p.1 ∈ Set.Icc (0 : ℝ) 1 →
      p.2 ∈ Submission.Drive.unitBox 2 → L 0 p.1 = D 0 p.2 →
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1)
    (hdim : Module.finrank ℝ (ℝ × EuclideanSpace ℝ (Fin 3)) = Module.finrank ℝ E)
    (hreg : ∀ p : ℝ × EuclideanSpace ℝ (Fin 3), p.1 ∈ Set.Icc (0 : ℝ) 1 →
      p.2 ∈ Submission.Drive.unitBox 2 → L 0 p.1 = D 0 p.2 →
      Function.Surjective
        (fderiv ℝ (fun q : ℝ × EuclideanSpace ℝ (Fin 3) => L 0 q.1 - D 0 q.2) p)) :
    ∀ᶠ s in nhds (0 : EuclideanSpace ℝ (Fin N)),
      (Work.Drive.meetBox (L s) (D s)).ncard = (Work.Drive.meetBox (L 0) (D 0)).ncard :=
  eventually_ncard_meetBox_eq_par L D hL hD hfin hint hdim hreg

end

end Work.Drive
