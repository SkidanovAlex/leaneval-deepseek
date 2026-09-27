import Mathlib
import Submission.Work.Drive.boxParity
import Submission.Work.Drive.bdry_label_parity

/-!
# Local constancy of the labelled boundary zero counts

Hugelmeyer's bookkeeping (`bdry_label_parity`) splits the boundary zeros of a family `G t` of maps
`ℝ^{m+1} → ℝ^m` into the pieces `labelMeet (G t) label s`, according to the face on which the zero
sits.  The mod-2 arguments need those *individual counts* to be locally constant in `t` near a
regular value: this file proves that, under the standing regularity hypotheses of
`Submission.Drive.ParityProp` at `t = 0`.

The proof has three layers.

* `exists_local_solution` is the implicit function theorem in the form needed: near a boundary zero
  `ξ` of `G 0` which lies on the face `x i = ξ i` transversally, and for every `t` in a fixed
  interval, the slice `{x | x i = ξ i}` of the zero set of `G t` meets a fixed ball around `ξ` in
  exactly one point `ψ t`, and `ψ` is continuous at `0` with `ψ 0 = ξ`.
  The device is the map `R (t,x) = (t, G t x, x i)` between spaces of the same dimension `m+2`,
  whose derivative at `(0,ξ)` is *surjective* (regularity of `G 0` at `ξ` plus the face
  transversality), hence bijective; the inverse function theorem at `(0,ξ)` then gives the unique
  solution of `R (t,x) = (t,0,ξ i)`.
* `eventually_bdyZeros_cover` is the soft half: for `t → 0` every boundary zero of `G t` is close
  to a boundary zero of `G 0` (compactness of the boundary of the box).
* `exists_pos_le_dist_of_finite` and `exists_face_forced` provide, per zero, a ball in which the
  face is forced and in which distinct zeros are separated, so that the solution map `ξ ↦ ψ_ξ t` is
  injective on the boundary zeros and the pieces of a fixed label match up.
-/

namespace Work.Drive

open Filter
open scoped Topology ContDiff

noncomputable section

/-- The boundary of the unit box is compact. -/
theorem isCompact_unitBoxBdry (m : ℕ) : IsCompact (Submission.Drive.unitBoxBdry m) :=
  (isCompact_unitBox m).of_isClosed_subset (isClosed_unitBoxBdry m) fun x hx => hx.1

/-- **The partial derivative of an uncurried family.**  If `f : ℝ × E → F` has derivative `f'` at
`(t₀,x₀)`, then the derivative of the partial map `y ↦ f (t₀, y)` at `x₀` is `f'` composed with the
inclusion of the second factor. -/
lemma fderiv_uncurry_snd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ × E → F} {f' : ℝ × E →L[ℝ] F}
    {t₀ : ℝ} {x₀ : E} (hf : HasFDerivAt f f' (t₀, x₀)) :
    fderiv ℝ (fun y : E => f (t₀, y)) x₀ = f' ∘L ContinuousLinearMap.inr ℝ ℝ E := by
  have h : HasFDerivAt (fun y : E => (t₀, y)) (ContinuousLinearMap.inr ℝ ℝ E) x₀ :=
    hasFDerivAt_prodMk_right t₀ x₀
  exact (hf.comp x₀ h).fderiv

/-- **Separation of the points of a finite set.**  A finite set in a normed group is uniformly
discrete: there is `ρ > 0` such that `2ρ` is a lower bound for the distance of distinct points. -/
theorem exists_pos_le_dist_of_finite {E : Type*} [NormedAddCommGroup E] {Z : Set E}
    (hZ : Z.Finite) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ξ ∈ Z, ∀ η ∈ Z, ξ ≠ η → 2 * ρ ≤ ‖ξ - η‖ := by
  classical
  by_cases h1 : ∀ ξ ∈ Z, ∀ η ∈ Z, ξ = η
  · exact ⟨1, one_pos, fun ξ hξ η hη hne => absurd (h1 ξ hξ η hη) hne⟩
  · push Not at h1
    obtain ⟨ξ₀, hξ₀, η₀, hη₀, hne₀⟩ := h1
    set T : Finset E := hZ.toFinset with hT
    have hTm : ∀ x, x ∈ T ↔ x ∈ Z := fun x => hZ.mem_toFinset
    have hmemoff : ∀ {a b : E}, a ∈ Z → b ∈ Z → a ≠ b → (a, b) ∈ T.offDiag := by
      intro a b ha hb hab
      rw [Finset.mem_offDiag]
      exact ⟨(hTm a).mpr ha, (hTm b).mpr hb, hab⟩
    set P : Finset ℝ := T.offDiag.image (fun p : E × E => ‖p.1 - p.2‖) with hP
    have hPne : P.Nonempty := ⟨_, Finset.mem_image_of_mem _ (hmemoff hξ₀ hη₀ hne₀)⟩
    have hPpos : 0 < P.min' hPne := by
      obtain ⟨p, hp, hval⟩ := Finset.mem_image.mp (Finset.min'_mem P hPne)
      rw [← hval]
      exact norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_offDiag.mp hp).2.2)
    refine ⟨P.min' hPne / 2, by linarith, ?_⟩
    intro ξ hξ η hη hξη
    have hmem : ‖ξ - η‖ ∈ P := by
      rw [hP]
      exact Finset.mem_image_of_mem _ (hmemoff hξ hη hξη)
    have hle : P.min' hPne ≤ ‖ξ - η‖ := Finset.min'_le P _ hmem
    linarith

/-- **Upper semicontinuity of the boundary zero set.**  Given a continuous family `G` and a positive
radius `δ ξ` at each boundary zero `ξ` of `G 0`, all boundary zeros of `G t` with `t` close to `0`
lie in the corresponding ball around a boundary zero of `G 0`. -/
theorem eventually_bdyZeros_cover {m : ℕ} {G : ℝ → Amb m → Tgt m}
    (hG : Continuous (fun p : ℝ × Amb m => G p.1 p.2)) {δ : bdyZeros (G 0) → ℝ}
    (hδ : ∀ ξ : bdyZeros (G 0), 0 < δ ξ) :
    ∀ᶠ t in nhds (0 : ℝ), ∀ x ∈ bdyZeros (G t),
      ∃ ξ : bdyZeros (G 0), ‖x - ξ.1‖ < δ ξ := by
  have key : ∃ ε > 0, ∀ t, |t| < ε → ∀ x ∈ bdyZeros (G t),
      ∃ ξ : bdyZeros (G 0), ‖x - ξ.1‖ < δ ξ := by
    by_contra hcon
    push Not at hcon
    have hseq : ∀ k : ℕ, ∃ t : ℝ, ∃ x : Amb m, |t| < 1 / (k + 1) ∧
        x ∈ bdyZeros (G t) ∧ ∀ ξ : bdyZeros (G 0), δ ξ ≤ ‖x - ξ.1‖ := by
      intro k
      obtain ⟨t, ht, x, hx, hfar⟩ := hcon (1 / (k + 1)) (by positivity)
      exact ⟨t, x, ht, hx, hfar⟩
    choose t x ht hx hfar using hseq
    have htend : Tendsto t atTop (nhds (0 : ℝ)) := by
      refine squeeze_zero_norm' (a := fun k : ℕ => 1 / ((k : ℝ) + 1)) ?_
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact Filter.Eventually.of_forall fun k => le_of_lt (ht k)
    have hxs : ∀ k, x k ∈ Submission.Drive.unitBoxBdry m := fun k => (hx k).1
    obtain ⟨y, hy, φ, hφ, hxtend⟩ := (isCompact_unitBoxBdry m).tendsto_subseq hxs
    have htφ : Tendsto (fun k => t (φ k)) atTop (nhds (0 : ℝ)) :=
      htend.comp hφ.tendsto_atTop
    have hpair : Tendsto (fun k => (t (φ k), x (φ k))) atTop (nhds ((0 : ℝ), y)) :=
      htφ.prodMk_nhds hxtend
    have h1 : Tendsto (fun k => G (t (φ k)) (x (φ k))) atTop (nhds (G 0 y)) :=
      (hG.continuousAt).tendsto.comp hpair
    have h2 : Tendsto (fun k => G (t (φ k)) (x (φ k))) atTop (nhds (0 : Tgt m)) :=
      tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun k => ((hx (φ k)).2).symm)
    have hGy : G 0 y = 0 := tendsto_nhds_unique h1 h2
    have hyZ : y ∈ bdyZeros (G 0) := ⟨hy, hGy⟩
    have hfar' : ∀ k, δ ⟨y, hyZ⟩ ≤ ‖x (φ k) - y‖ := fun k => hfar (φ k) ⟨y, hyZ⟩
    have hev : ∀ᶠ k in atTop, ‖x (φ k) - y‖ < δ ⟨y, hyZ⟩ :=
      hxtend.eventually (Metric.ball_mem_nhds y (hδ ⟨y, hyZ⟩))
    obtain ⟨k, hk⟩ := hev.exists
    exact absurd hk (not_lt.mpr (hfar' k))
  obtain ⟨ε, hε, h⟩ := key
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  refine h t ?_
  have : dist t 0 < ε := by simpa [Metric.mem_ball] using ht
  rwa [Real.dist_eq, sub_zero] at this

/-- **The face is forced in a ball.**  If `ξ i ∈ {0,1}` and all the other coordinates of `ξ` are
strictly inside `(0,1)`, then in a small ball around `ξ` all coordinates other than the `i`-th are
strictly inside `(0,1)`, so that a point of the box boundary in that ball lies on the face
`x i = ξ i`. -/
theorem exists_face_forced {m : ℕ} {ξ : Amb m} {i : Fin (m + 1)}
    (hi : ξ i = 0 ∨ ξ i = 1) (hint : ∀ j, j ≠ i → ξ j ∈ Set.Ioo (0:ℝ) 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ x : Amb m, ‖x - ξ‖ < r →
      (∀ j, j ≠ i → x j ∈ Set.Ioo (0:ℝ) 1) ∧ ((x i = 0 ∨ x i = 1) → x i = ξ i) := by
  have hIoo : ∀ᶠ x in nhds ξ, ∀ j : Fin (m+1), j ≠ i → x j ∈ Set.Ioo (0:ℝ) 1 := by
    rw [Filter.eventually_all]
    intro j
    by_cases hji : j = i
    · subst hji
      exact Filter.Eventually.of_forall fun x h => absurd rfl h
    · exact Filter.Eventually.mono
        ((isOpen_Ioo.preimage (by fun_prop : Continuous (fun x : Amb m => x j))).mem_nhds
          (hint j hji)) (fun x hx _ => hx)
  obtain ⟨r₁, hr₁, hr₁'⟩ := Metric.mem_nhds_iff.mp hIoo
  refine ⟨min r₁ (1/2), lt_min hr₁ (by norm_num), ?_⟩
  intro x hx
  have hcoord : |x i - ξ i| ≤ ‖x - ξ‖ := by
    have h := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin (m+1) => ℝ) (x - ξ) i
    simpa using h
  refine ⟨?_, ?_⟩
  · intro j hj
    have hb : x ∈ Metric.ball ξ r₁ := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact lt_of_lt_of_le hx (min_le_left _ _)
    exact hr₁' hb j hj
  · intro hxi
    have hlt : |x i - ξ i| < 1/2 :=
      lt_of_le_of_lt hcoord (lt_of_lt_of_le hx (min_le_right _ _))
    rcases hi with h | h <;> rcases hxi with h' | h' <;>
      (rw [h, h'] at hlt ⊢ <;> norm_num at hlt)

/-- **The local solution of the sliced equation.**  Let `G` be a smooth family of maps
`ℝ^{m+1} → ℝ^m`, with `0` a regular value of `G 0` on the unit box and with every boundary zero of
`G 0` transverse to its (unique) face.  If `ξ` is a boundary zero of `G 0` on the face
`x i = ξ i` (transversally), then there is a ball around `ξ` and an interval around `t = 0` such
that for every `t` in that interval the zero set of `G t` meets the hyperplane `x i = ξ i` in the
ball in exactly one point `ψ t`; moreover `ψ 0 = ξ` and `ψ` is continuous at `0`.

The proof applies the inverse function theorem to the map `R (t,x) = (t, G t x, x i)`, from the
`(m+2)`-dimensional space `ℝ × ℝ^{m+1}` to the `(m+2)`-dimensional space `ℝ × ℝ^m × ℝ`.  Its
derivative at `(0,ξ)` is an isomorphism: the derivative of `G 0` at `ξ` is surjective, its kernel is
spanned by the cofactor vector `cofactorVec`, which does not lie in the hyperplane `v i = 0`
precisely because the face is transverse. -/
theorem exists_local_solution {m : ℕ} (G : ℝ → Amb m → Tgt m)
    (hG : ContDiff ℝ Ctop (fun p : ℝ × Amb m => G p.1 p.2))
    (hreg : ∀ x ∈ Submission.Drive.unitBox m, G 0 x = 0 →
      Function.Surjective (fderiv ℝ (G 0) x))
    {ξ : Amb m} (hξbox : ξ ∈ Submission.Drive.unitBox m) (hξ0 : G 0 ξ = 0)
    {i : Fin (m + 1)}
    (hsurj : Function.Surjective (fun v : {v : Amb m // v i = 0} =>
      fderiv ℝ (G 0) ξ v.1)) :
    ∃ (ε δ : ℝ) (ψ : ℝ → Amb m), 0 < ε ∧ 0 < δ ∧ ψ 0 = ξ ∧
      Filter.Tendsto ψ (nhds (0 : ℝ)) (nhds ξ) ∧
      (∀ t, |t| < ε → ‖ψ t - ξ‖ < δ ∧ ψ t i = ξ i ∧ G t (ψ t) = 0) ∧
      (∀ t, |t| < ε → ∀ x, ‖x - ξ‖ < δ → x i = ξ i → G t x = 0 → x = ψ t) := by
  classical
  set uncG : ℝ × Amb m → Tgt m := fun p => G p.1 p.2 with huncG
  have huncGcd : ContDiff ℝ Ctop uncG := hG
  have hne : Ctop ≠ 0 := by decide
  have huncGat : HasFDerivAt uncG (fderiv ℝ uncG (0, ξ)) (0, ξ) :=
    (huncGcd.contDiffAt.differentiableAt hne).hasFDerivAt
  have hD : Function.Surjective (fderiv ℝ (G 0) ξ) := hreg ξ hξbox hξ0
  have hPD : fderiv ℝ (G 0) ξ =
      (fderiv ℝ uncG (0, ξ)) ∘L ContinuousLinearMap.inr ℝ ℝ (Amb m) := by
    have h := fderiv_uncurry_snd huncGat
    simpa [huncG] using h
  set R : ℝ × Amb m → ℝ × Tgt m × ℝ := fun p => (p.1, uncG p, p.2 i) with hRdef
  set L1 : ℝ × Amb m →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (Amb m) with hL1
  set L2 : ℝ × Amb m →L[ℝ] Tgt m := fderiv ℝ uncG (0, ξ) with hL2
  set L3 : ℝ × Amb m →L[ℝ] ℝ :=
    (coordL i) ∘L (ContinuousLinearMap.snd ℝ ℝ (Amb m)) with hL3
  set L : ℝ × Amb m →L[ℝ] ℝ × Tgt m × ℝ := L1.prod (L2.prod L3) with hL
  have hLc : ∀ p : ℝ × Amb m, L p = (L1 p, L2 p, L3 p) := by
    intro p; simp [hL, ContinuousLinearMap.prod_apply]
  have hL1_apply : ∀ p : ℝ × Amb m, L1 p = p.1 := fun p => rfl
  have hL3_apply : ∀ p : ℝ × Amb m, L3 p = p.2 i := fun p => by simp [hL3]
  have hRfd : HasFDerivAt R L (0, ξ) := by
    have h1 : HasFDerivAt (fun p : ℝ × Amb m => p.1) L1 (0, ξ) := hasFDerivAt_fst
    have h2 : HasFDerivAt uncG L2 (0, ξ) := huncGat
    have h3 : HasFDerivAt (fun p : ℝ × Amb m => p.2 i) L3 (0, ξ) := by
      have hs : HasFDerivAt (fun p : ℝ × Amb m => p.2)
          (ContinuousLinearMap.snd ℝ ℝ (Amb m)) (0, ξ) := hasFDerivAt_snd
      have hc : HasFDerivAt (fun y : Amb m => y i) (coordL i) ξ := coordL_hasFDerivAt i ξ
      exact hc.comp (0, ξ) hs
    exact h1.prodMk (h2.prodMk h3)
  have hkey : ∀ (a : ℝ) (v : Amb m),
      L2 (a, v) = a • L2 ((1:ℝ), (0:Amb m)) + fderiv ℝ (G 0) ξ v := by
    intro a v
    have hsplit : (a, v) = a • ((1:ℝ), (0:Amb m)) + ((0:ℝ), v) := by ext <;> simp
    rw [hsplit, map_add, map_smul]
    congr 1
    rw [hPD]
    rfl
  have hLsurj : Function.Surjective L := by
    intro y
    obtain ⟨a, b, r⟩ := y
    set κ : Amb m := cofactorVec (fderiv ℝ (G 0) ξ) with hκ
    have hκi : κ i ≠ 0 := by
      rw [hκ]
      exact cofactorVec_apply_ne_zero (fderiv ℝ (G 0) ξ) i hsurj
    have hκker : fderiv ℝ (G 0) ξ κ = 0 := by
      rw [hκ]; exact cofactorVec_mem_ker _
    obtain ⟨v', hv'⟩ := hD (b - a • L2 ((1:ℝ), (0:Amb m)))
    refine ⟨(a, v' + ((r - v' i) / κ i) • κ), ?_⟩
    have hL2v : L2 (a, v' + ((r - v' i) / κ i) • κ) = b := by
      rw [hkey]
      have hDv : fderiv ℝ (G 0) ξ (v' + ((r - v' i) / κ i) • κ)
          = b - a • L2 ((1:ℝ), (0:Amb m)) := by
        rw [map_add, map_smul, hv', hκker, smul_zero, add_zero]
      rw [hDv]; abel
    have hL3v : L3 (a, v' + ((r - v' i) / κ i) • κ) = r := by
      rw [hL3_apply]
      have h1 : (v' + ((r - v' i) / κ i) • κ) i = v' i + ((r - v' i) / κ i) * κ i := by
        simp [PiLp.add_apply, PiLp.smul_apply]
      rw [h1, div_mul_cancel₀ _ hκi]
      ring
    rw [hLc, hL1_apply, hL2v, hL3v]
  have hLinj : Function.Injective L := by
    rintro ⟨s, v⟩ ⟨s', v'⟩ heq
    have h1 : s = s' := by
      have := congrArg (fun z : ℝ × Tgt m × ℝ => z.1) heq
      simpa [hLc, hL1_apply] using this
    have h3 : v i = v' i := by
      have := congrArg (fun z : ℝ × Tgt m × ℝ => z.2.2) heq
      simpa [hLc, hL3_apply] using this
    set κ : Amb m := cofactorVec (fderiv ℝ (G 0) ξ) with hκ
    have hκi : κ i ≠ 0 := by
      rw [hκ]
      exact cofactorVec_apply_ne_zero (fderiv ℝ (G 0) ξ) i hsurj
    have h2 : fderiv ℝ (G 0) ξ (v - v') = 0 := by
      have hthis := congrArg (fun z : ℝ × Tgt m × ℝ => z.2.1) heq
      have h2a : L2 (s, v) = L2 (s', v') := by simpa [hLc] using hthis
      have h2aL := hkey s v
      have h2aR := hkey s' v'
      rw [h2aL, h2aR, h1] at h2a
      have h2b : fderiv ℝ (G 0) ξ v = fderiv ℝ (G 0) ξ v' := add_left_cancel h2a
      rw [map_sub, h2b, sub_self]
    have hmem : v - v' ∈ (fderiv ℝ (G 0) ξ).ker := h2
    rw [ker_eq_span_cofactorVec _ hD] at hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hci : c * κ i = 0 := by
      have h := congrArg (fun w : Amb m => w i) hc
      simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at h
      rw [h3, sub_self] at h
      exact h
    have hc0 : c = 0 := by
      rcases mul_eq_zero.mp hci with h | h
      · exact h
      · exact absurd h hκi
    have hvv : v = v' := by
      have : v - v' = 0 := by rw [← hc, hc0, zero_smul]
      exact sub_eq_zero.mp this
    exact Prod.ext h1 hvv
  have hRcd : ContDiff ℝ Ctop R := by
    rw [hRdef]; fun_prop
  have hstL : HasStrictFDerivAt R (fderiv ℝ R (0, ξ)) (0, ξ) := hRcd.hasStrictFDerivAt hne
  have hfdeq : fderiv ℝ R (0, ξ) = L := hRfd.fderiv
  have hbij : Function.Bijective (L : ℝ × Amb m →ₗ[ℝ] ℝ × Tgt m × ℝ) := ⟨hLinj, hLsurj⟩
  let e := (LinearEquiv.ofBijective (L : ℝ × Amb m →ₗ[ℝ] ℝ × Tgt m × ℝ) hbij).toContinuousLinearEquiv
  have he : (e : ℝ × Amb m →L[ℝ] ℝ × Tgt m × ℝ) = L := by
    apply ContinuousLinearMap.ext; intro x; rfl
  have hst : HasStrictFDerivAt R (e : ℝ × Amb m →L[ℝ] ℝ × Tgt m × ℝ) (0, ξ) := by
    rw [he, ← hfdeq]
    exact hstL
  let Φ : OpenPartialHomeomorph (ℝ × Amb m) (ℝ × Tgt m × ℝ) :=
    HasStrictFDerivAt.toOpenPartialHomeomorph R hst
  have hΦcoe : (Φ : ℝ × Amb m → ℝ × Tgt m × ℝ) = R :=
    HasStrictFDerivAt.toOpenPartialHomeomorph_coe hst
  have hsrc : (0, ξ) ∈ Φ.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source hst
  have htgt : R (0, ξ) ∈ Φ.target :=
    HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target hst
  have hR0 : R (0, ξ) = (0, (0 : Tgt m), ξ i) := by simp [hRdef, huncG, hξ0]
  have htgt0 : ((0:ℝ), (0:Tgt m), ξ i) ∈ Φ.target := by rwa [← hR0]
  obtain ⟨r_src, hr_src, hr_src'⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hsrc)
  have htgt_nhds : ∀ᶠ t in nhds (0:ℝ), (t, (0:Tgt m), ξ i) ∈ Φ.target := by
    have hcont : ContinuousAt (fun t : ℝ => (t, (0:Tgt m), ξ i)) 0 := by fun_prop
    exact hcont.preimage_mem_nhds (Φ.open_target.mem_nhds htgt0)
  obtain ⟨r_tgt, hr_tgt, hr_tgt'⟩ := Metric.mem_nhds_iff.mp htgt_nhds
  have hsymm0 : Φ.symm ((0:ℝ), (0:Tgt m), ξ i) = (0, ξ) := by
    have h := Φ.left_inv hsrc
    rw [hΦcoe, hR0] at h
    exact h
  set ψ : ℝ → Amb m := fun t => (Φ.symm (t, (0:Tgt m), ξ i)).2 with hψ
  have hψ0 : ψ 0 = ξ := by simp [hψ, hsymm0]
  have hψcont : Filter.Tendsto ψ (nhds (0:ℝ)) (nhds ξ) := by
    have hcont : ContinuousAt (fun t : ℝ => (t, (0:Tgt m), ξ i)) 0 := by fun_prop
    have hs : Filter.Tendsto (fun t : ℝ => Φ.symm (t, (0:Tgt m), ξ i)) (nhds (0:ℝ))
        (nhds (Φ.symm ((0:ℝ), (0:Tgt m), ξ i))) :=
      (Φ.continuousAt_symm htgt0).tendsto.comp hcont.tendsto
    rw [hsymm0] at hs
    exact (continuous_snd.continuousAt.tendsto).comp hs
  obtain ⟨r_ψ, hr_ψ, hr_ψ'⟩ := Metric.mem_nhds_iff.mp
    (hψcont.eventually (Metric.ball_mem_nhds ξ hr_src))
  refine ⟨min r_tgt (min r_src r_ψ), r_src, ψ, lt_min hr_tgt (lt_min hr_src hr_ψ),
    hr_src, hψ0, hψcont, ?_, ?_⟩
  · intro t ht
    have ht_tgt : |t| < r_tgt := lt_of_lt_of_le ht (min_le_left _ _)
    have ht_ψ : |t| < r_ψ :=
      lt_of_lt_of_le ht (le_trans (min_le_right _ _) (min_le_right _ _))
    have hmem_tgt : (t, (0 : Tgt m), ξ i) ∈ Φ.target :=
      hr_tgt' (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact ht_tgt)
    have hRsol : R (Φ.symm (t, (0:Tgt m), ξ i)) = (t, (0:Tgt m), ξ i) := by
      rw [← hΦcoe]; exact Φ.right_inv hmem_tgt
    have h1 : (Φ.symm (t, (0:Tgt m), ξ i)).1 = t := by
      have := congrArg (fun z : ℝ × Tgt m × ℝ => z.1) hRsol
      simpa [hRdef] using this
    have h2 : uncG (Φ.symm (t, (0:Tgt m), ξ i)) = 0 := by
      have := congrArg (fun z : ℝ × Tgt m × ℝ => z.2.1) hRsol
      simpa [hRdef] using this
    have h3 : (Φ.symm (t, (0:Tgt m), ξ i)).2 i = ξ i := by
      have := congrArg (fun z : ℝ × Tgt m × ℝ => z.2.2) hRsol
      simpa [hRdef] using this
    have hnorm : ‖ψ t - ξ‖ < r_src := by
      have hm := hr_ψ' (by rw [Metric.mem_ball, Real.dist_eq, sub_zero]; exact ht_ψ)
      simpa [Set.mem_ofPred_eq, dist_eq_norm] using hm
    refine ⟨hnorm, h3, ?_⟩
    have hun : uncG (Φ.symm (t, (0:Tgt m), ξ i)) = G t (ψ t) := by
      simp [huncG, hψ, h1]
    rw [← hun]; exact h2
  · intro t ht x hx hxi hx0
    have ht_src : |t| < r_src :=
      lt_of_lt_of_le ht (le_trans (min_le_right _ _) (min_le_left _ _))
    have hball : ((t, x) : ℝ × Amb m) ∈ Metric.ball ((0, ξ) : ℝ × Amb m) r_src := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt (by rw [Real.dist_eq, sub_zero]; exact ht_src) (by rw [dist_eq_norm]; exact hx)
    have hinsrc : (t, x) ∈ Φ.source := hr_src' hball
    have hΦtx : Φ (t, x) = (t, (0:Tgt m), ξ i) := by
      rw [hΦcoe]
      have hRt : R (t, x) = (t, G t x, x i) := by simp [hRdef, huncG]
      rw [hRt, hx0, hxi]
    have hleft := Φ.left_inv hinsrc
    rw [hΦtx] at hleft
    have hfin : (Φ.symm (t, (0:Tgt m), ξ i)).2 = x := by
      have := congrArg (fun z : ℝ × Amb m => z.2) hleft
      simpa using this
    exact hfin.symm

/-- **The labelled counts of the boundary zeros are locally constant.**  Let `G : ℝ → ℝ^{m+1} →
ℝ^m` be a smooth family, `0` a regular value of `G 0` on the unit box, and every boundary zero of
`G 0` transverse to its unique face (the hypotheses of `Submission.Drive.ParityProp` at `t = 0`).
Then for `t` close to `0` and every label `s`, the number of boundary zeros of `G t` lying on a face
of label `s` equals the corresponding number for `G 0`. -/
theorem locallyConstant_labelMeet_eq (m : ℕ) {σ : Type*} (G : ℝ → Work.Drive.Amb m → Work.Drive.Tgt m)
    (label : Fin (m + 1) → σ)
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × Work.Drive.Amb m => G p.1 p.2))
    (hreg : ∀ x ∈ Submission.Drive.unitBox m, G 0 x = 0 →
      Function.Surjective (fderiv ℝ (G 0) x))
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry m, G 0 x = 0 → ∃ i : Fin (m + 1),
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
      Function.Surjective (fun v : {v : Work.Drive.Amb m // v i = 0} => fderiv ℝ (G 0) x v.1)) :
    Filter.Eventually (fun t : ℝ => ∀ s : σ,
      (Work.Drive.labelMeet (G t) label s).ncard
        = (Work.Drive.labelMeet (G 0) label s).ncard) (nhds (0 : ℝ)) := by
  classical
  have hG0 : ContDiff ℝ Ctop (G 0) := by
    have h : ContDiff ℝ Ctop
        ((fun p : ℝ × Amb m => G p.1 p.2) ∘ (fun x : Amb m => ((0:ℝ), x))) :=
      hG.comp (by fun_prop : ContDiff ℝ Ctop (fun x : Amb m => ((0:ℝ), x)))
    simpa [Function.comp_def] using h
  have hZfin : (bdyZeros (G 0)).Finite := bdyZeros_finite hG0 hface
  haveI : Finite (bdyZeros (G 0)) := hZfin.to_subtype
  -- the face of each boundary zero of `G 0`
  have hfaceZ : ∀ ξ : bdyZeros (G 0), ∃ i : Fin (m+1), (ξ.1 i = 0 ∨ ξ.1 i = 1) ∧
      (∀ j, j ≠ i → ξ.1 j ∈ Set.Ioo (0:ℝ) 1) ∧
      Function.Surjective (fun v : {v : Amb m // v i = 0} => fderiv ℝ (G 0) ξ.1 v.1) :=
    fun ξ => hface ξ.1 ξ.2.1 ξ.2.2
  choose iZ hZ01 hZint hZsurj using hfaceZ
  -- the local solution at each boundary zero
  have hloc : ∀ ξ : bdyZeros (G 0), ∃ (ε δ : ℝ) (ψ : ℝ → Amb m),
      0 < ε ∧ 0 < δ ∧ ψ 0 = ξ.1 ∧ Filter.Tendsto ψ (nhds (0:ℝ)) (nhds ξ.1) ∧
      (∀ t, |t| < ε → ‖ψ t - ξ.1‖ < δ ∧ ψ t (iZ ξ) = ξ.1 (iZ ξ) ∧ G t (ψ t) = 0) ∧
      (∀ t, |t| < ε → ∀ x, ‖x - ξ.1‖ < δ → x (iZ ξ) = ξ.1 (iZ ξ) → G t x = 0 → x = ψ t) :=
    fun ξ => exists_local_solution G hG hreg ξ.2.1.1 ξ.2.2 (hZsurj ξ)
  choose ε₀ δ₀ ψ₀ hε₀ hδ₀ hψ₀ hcont₀ hmain₀ huniq₀ using hloc
  -- separation radius
  obtain ⟨ρ, hρpos, hρ⟩ := exists_pos_le_dist_of_finite hZfin
  -- radius in which the face is forced
  have hff : ∀ ξ : bdyZeros (G 0), ∃ r : ℝ, 0 < r ∧ ∀ x : Amb m, ‖x - ξ.1‖ < r →
      (∀ j, j ≠ iZ ξ → x j ∈ Set.Ioo (0:ℝ) 1) ∧
      ((x (iZ ξ) = 0 ∨ x (iZ ξ) = 1) → x (iZ ξ) = ξ.1 (iZ ξ)) :=
    fun ξ => exists_face_forced (hZ01 ξ) (hZint ξ)
  choose rf hrfpos hrf using hff
  -- the radii actually used
  set δZ : bdyZeros (G 0) → ℝ := fun ξ => min (δ₀ ξ) (min (rf ξ) ρ) with hδZdef
  have hδZval : ∀ ξ, δZ ξ = min (δ₀ ξ) (min (rf ξ) ρ) := fun ξ => rfl
  have hδZpos : ∀ ξ, 0 < δZ ξ := by
    intro ξ
    rw [hδZval]
    exact lt_min (hδ₀ ξ) (lt_min (hrfpos ξ) hρpos)
  have hδZ_le_δ₀ : ∀ ξ, δZ ξ ≤ δ₀ ξ := fun ξ =>
    le_of_eq (hδZval ξ) |>.trans (min_le_left _ _)
  have hδZ_le_rf : ∀ ξ, δZ ξ ≤ rf ξ := fun ξ =>
    le_of_eq (hδZval ξ) |>.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδZ_le_ρ : ∀ ξ, δZ ξ ≤ ρ := fun ξ =>
    le_of_eq (hδZval ξ) |>.trans ((min_le_right _ _).trans (min_le_right _ _))
  -- the three eventual statements
  have hevA : ∀ᶠ t in nhds (0:ℝ), ∀ ξ : bdyZeros (G 0),
      ‖ψ₀ ξ t - ξ.1‖ < δZ ξ ∧ ψ₀ ξ t (iZ ξ) = ξ.1 (iZ ξ) ∧ G t (ψ₀ ξ t) = 0 := by
    rw [Filter.eventually_all]
    intro ξ
    have h1 : ∀ᶠ t in nhds (0:ℝ), |t| < ε₀ ξ := by
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) (hε₀ ξ)] with t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht
    have h2 : ∀ᶠ t in nhds (0:ℝ), ‖ψ₀ ξ t - ξ.1‖ < δZ ξ := by
      have hc := (hcont₀ ξ).eventually (Metric.ball_mem_nhds ξ.1 (hδZpos ξ))
      filter_upwards [hc] with t ht
      simpa [dist_eq_norm] using ht
    filter_upwards [h1, h2] with t ht1 ht2
    exact ⟨ht2, (hmain₀ ξ t ht1).2.1, (hmain₀ ξ t ht1).2.2⟩
  have hevB : ∀ᶠ t in nhds (0:ℝ), ∀ x ∈ bdyZeros (G t),
      ∃ ξ : bdyZeros (G 0), ‖x - ξ.1‖ < δZ ξ :=
    eventually_bdyZeros_cover hG.continuous hδZpos
  have hevC : ∀ᶠ t in nhds (0:ℝ), ∀ ξ : bdyZeros (G 0), ∀ x, ‖x - ξ.1‖ < δZ ξ →
      x (iZ ξ) = ξ.1 (iZ ξ) → G t x = 0 → x = ψ₀ ξ t := by
    rw [Filter.eventually_all]
    intro ξ
    have h1 : ∀ᶠ t in nhds (0:ℝ), |t| < ε₀ ξ := by
      filter_upwards [Metric.ball_mem_nhds (0:ℝ) (hε₀ ξ)] with t ht
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
      exact ht
    filter_upwards [h1] with t ht1 x hx hxi hx0
    exact huniq₀ ξ t ht1 x (lt_of_lt_of_le hx (hδZ_le_δ₀ ξ)) hxi hx0
  -- now the conclusion holds for all sufficiently small `t`
  filter_upwards [hevA, hevB, hevC] with t hA hB hC
  intro s
  -- the parametrisation of the boundary zeros of `G t` by those of `G 0`
  set Ψ : (bdyZeros (G 0)) → Amb m := fun ξ => ψ₀ ξ t with hΨdef
  have hΨval : ∀ ξ : bdyZeros (G 0), Ψ ξ = ψ₀ ξ t := fun ξ => rfl
  -- the coordinates of `Ψ ξ` equal to `0` or `1` are exactly the `iZ ξ`-th one
  have hcoordΨ : ∀ (ξ : bdyZeros (G 0)) (j : Fin (m+1)),
      (Ψ ξ j = 0 ∨ Ψ ξ j = 1) → j = iZ ξ := by
    intro ξ j hj
    by_contra hne
    have h1 := (hrf ξ (Ψ ξ)) (lt_of_lt_of_le (hA ξ).1 (hδZ_le_rf ξ))
    have h2 := h1.1 j hne
    rcases hj with h | h
    · rw [h] at h2; exact absurd h2.1 (by norm_num)
    · rw [h] at h2; exact absurd h2.2 (by norm_num)
  have hΨmem : ∀ ξ : bdyZeros (G 0), Ψ ξ ∈ bdyZeros (G t) := by
    intro ξ
    have hfr := (hrf ξ (Ψ ξ)) (lt_of_lt_of_le (hA ξ).1 (hδZ_le_rf ξ))
    have h01 : Ψ ξ (iZ ξ) = 0 ∨ Ψ ξ (iZ ξ) = 1 := by
      rw [hΨval, (hA ξ).2.1]
      exact hZ01 ξ
    refine ⟨⟨fun j => ?_, ⟨iZ ξ, h01⟩⟩, (hA ξ).2.2⟩
    by_cases hj : j = iZ ξ
    · subst hj
      rcases h01 with h | h <;> rw [h] <;> norm_num
    · exact Set.Ioo_subset_Icc_self (hfr.1 j hj)
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
  have hΨsurj : ∀ x ∈ bdyZeros (G t), ∃ ξ : bdyZeros (G 0), Ψ ξ = x := by
    intro x hx
    obtain ⟨ξ, hdist⟩ := hB x hx
    refine ⟨ξ, ?_⟩
    have hfr := (hrf ξ x) (lt_of_lt_of_le hdist (hδZ_le_rf ξ))
    have hxi : x (iZ ξ) = ξ.1 (iZ ξ) := by
      obtain ⟨-, j, hj⟩ := hx.1
      have hji : j = iZ ξ := by
        by_contra hne
        have h2 := hfr.1 j hne
        rcases hj with h | h
        · rw [h] at h2; exact absurd h2.1 (by norm_num)
        · rw [h] at h2; exact absurd h2.2 (by norm_num)
      rw [hji] at hj
      exact hfr.2 hj
    exact (hC ξ x hdist hxi hx.2).symm
  -- the labels of the parametrised points
  have hkeyt : ∀ ξ : bdyZeros (G 0), (Ψ ξ ∈ labelMeet (G t) label s ↔ label (iZ ξ) = s) := by
    intro ξ
    constructor
    · intro h
      obtain ⟨-, j, hj, hxj⟩ := h
      have hji : j = iZ ξ := hcoordΨ ξ j hxj
      rw [← hji]; exact hj
    · intro h
      exact ⟨hΨmem ξ, iZ ξ, h, by rw [hΨval, (hA ξ).2.1]; exact hZ01 ξ⟩
  have hkey0 : ∀ ξ : bdyZeros (G 0), (ξ.1 ∈ labelMeet (G 0) label s ↔ label (iZ ξ) = s) := by
    intro ξ
    constructor
    · intro h
      obtain ⟨-, j, hj, hxj⟩ := h
      have hji : j = iZ ξ := by
        by_contra hne
        have h2 := hZint ξ j hne
        rcases hxj with h' | h'
        · rw [h'] at h2; exact absurd h2.1 (by norm_num)
        · rw [h'] at h2; exact absurd h2.2 (by norm_num)
      rw [← hji]; exact hj
    · intro h
      exact ⟨ξ.2, iZ ξ, h, hZ01 ξ⟩
  have hset : labelMeet (G t) label s = Ψ '' {ξ : bdyZeros (G 0) | label (iZ ξ) = s} := by
    ext x
    constructor
    · intro hx
      obtain ⟨ξ, hξeq⟩ := hΨsurj x hx.1
      exact ⟨ξ, (hkeyt ξ).mp (by rwa [hξeq]), hξeq⟩
    · rintro ⟨ξ, hξ, rfl⟩
      exact (hkeyt ξ).mpr hξ
  have hset0 : labelMeet (G 0) label s
      = Subtype.val '' {ξ : bdyZeros (G 0) | label (iZ ξ) = s} := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨x, hx.1⟩, (hkey0 ⟨x, hx.1⟩).mp hx, rfl⟩
    · rintro ⟨ξ, hξ, rfl⟩
      exact (hkey0 ξ).mpr hξ
  rw [hset, hset0, Set.ncard_image_of_injective (f := Ψ) _ hΨinj,
    Set.ncard_image_of_injective (f := Subtype.val) _ Subtype.val_injective]

end

end Work.Drive
