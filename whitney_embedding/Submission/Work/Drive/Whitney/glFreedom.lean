import Mathlib
import Submission.Work.Drive.Whitney.gU_det_interface
import Submission.Work.Drive.Whitney.gU_smooth
import Submission.Work.Drive.Whitney.exists_diffeo_maps_two_points

/-!
# The `GL(E)`-freedom route to `glAuxCore`

The `gU`-ansatz of `glAuxCoreDefs` builds the operator family out of `u`, `w` and a *vector field*
`ψ ⊥ u`; on the square the determinant is `(α + Θ)/(1 + Θ)` with `Θ = ‖gChi‖²`, and this forced
`gChi` to be nowhere zero on `{α ≤ 0}` — a condition that is **refuted** (`opTSquare_refute.lean`,
`exists_psi_of_coefA_refute.lean`, and `Submission/Work/Drive/Whitney/NOTES_det_gU_consumer.md` §5).
The winding obstruction behind that refutation is exactly the rigidity of the `(2,2)` block
`gCfam = (1 - gPu) + z ⊗ χ`: it is a *rank-one* modification of the projection onto `u^⊥`.

This file takes the `GL(E)`-freedom route.  The operator is written

  `gUB φ u w B = gAl • 1 + gJ + (B - gAl • 1) * (1 - gPu)`,

i.e. the same family as `gU`, but with the whole `(2,2)` block `gCfam` replaced by an **arbitrary
smooth family `B` of endomorphisms** (the "free corrector").  Then

* `gUB_apply_u`: on the square `gUB φ u w B p (u p) = w p` — for **every** `B`, with no condition
  on `B` at all (the rigidity of the ansatz is gone);
* `gUB_eq_one_of_apply_eq`: at a point with `φ = 1`, `u p = w p ≠ 0` and `B p = 1` the family
  is `1` (so the free corrector is `1` on the edges);
* `contDiff_gUB`: smoothness of the family from smoothness of `φ`, `u`, `w`, `B`;
* `exists_isUnit_apply_eq` and `exists_isUnit_factor`: the pointwise `GL(E)`-freedom — a unit
  sending `u` to `w` always exists, and any two such units differ by a unit fixing `u`
  (`GL(E)` acts on `{A : A u = w}` with the stabiliser of `u` as structure group);
* `glAuxCore_of_freeCorrector`: **the reduction** — `glAuxCore` follows from the existence, for
  every admissible `(u,w)`, of a cutoff `φ` and a free corrector `B` which is a unit on the square,
  whose complement `B` equals `1` on the two edges, and for which `gUB φ u w B` is a unit on the
  square.  Everything else (`gUB` being smooth, acting by `u ↦ w`, and being `1` on the edges) is
  *proved*, not assumed; the corrector only has to be chosen so that the *determinant* of `gUB` is
  nonvanishing, which by `isUnit_clm_iff_det_ne_zero` is the single scalar-free condition left.
-/

namespace Work.Drive.Whitney

open scoped RealInnerProductSpace ContDiff Topology
open Set

variable {m : ℕ}

/-! ## The free-corrector family -/

/-- **The `gU` family with a free `(2,2)` block.**  Replacing the rank-one correction `gCfam` of
`glAuxCoreDefs` by an arbitrary smooth family `B` of endomorphisms. -/
noncomputable def gUB (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (B : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :
    ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  fun p => gAl φ u w p • 1 + gJ φ u w p + (B p - gAl φ u w p • 1) * (1 - gPu φ u p)

/-- The formula of `glAuxCoreDefs` is the special case of the free family with the corrector
`gCfam`. -/
lemma gU_eq_gUB (φ : ℝ × ℝ → ℝ) (u w ψ : ℝ × ℝ → EuclideanSpace ℝ (Fin m)) :
    gU φ u w ψ = gUB φ u w (gCfam φ u w ψ) := rfl

/-- **Pointwise `GL(E)`-freedom**: for non-zero `u`, `w` there is a unit sending `u` to `w`. -/
theorem exists_isUnit_apply_eq (u w : EuclideanSpace ℝ (Fin m)) (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m), IsUnit A ∧ A u = w := by
  obtain ⟨R, ρ, hρ, hR⟩ := exists_linearIsometryEquiv_smul_eq u w hu hw
  refine ⟨(R : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)).comp
    (ρ • (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))), ?_, ?_⟩
  · rw [ContinuousLinearMap.isUnit_iff_bijective]
    refine ⟨?_, ?_⟩
    · intro x y hxy
      simp only [ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self] at hxy
      exact smul_right_injective _ hρ.ne' (R.injective hxy)
    · intro y
      refine ⟨ρ⁻¹ • R.symm y, ?_⟩
      simp only [ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self]
      rw [smul_inv_smul₀ hρ.ne']
      exact R.apply_symm_apply y
  · simp only [ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self]
    exact hR

/-- **The stabiliser torsor**: two units sending `u` to `w` differ by a unit fixing `u`. -/
theorem exists_isUnit_factor (u w : EuclideanSpace ℝ (Fin m))
    (A B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hA : IsUnit A) (hB : IsUnit B) (hAu : A u = w) (hBu : B u = w) :
    ∃ C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
      IsUnit C ∧ C u = u ∧ B = A * C := by
  obtain ⟨A', hA'⟩ := hA
  refine ⟨↑(A'⁻¹) * B, (A'⁻¹.isUnit).mul hB, ?_, ?_⟩
  · rw [mul_apply_eq_comp, hBu, ← hAu, ← hA', ← mul_apply_eq_comp, Units.inv_mul,
      one_apply_eq_self]
  · rw [← hA', ← mul_assoc, Units.mul_inv, one_mul]

/-! ## The free family acts by `u ↦ w`, and is `1` where `B = 1` and `u = w` -/

/-- On the square the free family sends `u` to `w`, for **every** corrector `B`. -/
theorem gUB_apply_u (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (B : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (p : ℝ × ℝ) (hφp : φ p = 1) (hup : u p ≠ 0) :
    gUB φ u w B p (u p) = w p := by
  have hISL : ∀ x y : EuclideanSpace ℝ (Fin m), (innerSL ℝ x) y = inner ℝ x y :=
    fun x y => rfl
  have hAm_in : gAm φ u p = inner ℝ (u p) (u p) := by
    simp only [gAm, hφp, one_mul, sub_self, add_zero]
  have hup_ne : inner ℝ (u p) (u p) ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hup)
  have hna : inner ℝ (gNn φ u w p) (u p) = 0 := by
    rw [gNn, gAl, inner_sub_left, real_inner_smul_left, hAm_in]
    rw [div_mul_cancel₀ _ hup_ne, sub_self]
  have hJ : gJ φ u w p (u p) = gNn φ u w p := by
    rw [gJ]
    simp only [smul_apply, sub_apply, ContinuousLinearMap.smulRight_apply, hISL]
    rw [hAm_in, hna, zero_smul, sub_zero, smul_smul, inv_mul_cancel₀ hup_ne, one_smul]
  have hPu : gPu φ u p (u p) = u p := by
    rw [gPu]
    simp only [smul_apply, ContinuousLinearMap.smulRight_apply, hISL]
    rw [hAm_in, smul_smul, inv_mul_cancel₀ hup_ne, one_smul]
  have h1mPu : u p - gPu φ u p (u p) = 0 := by rw [hPu, sub_self]
  have hB0 : (B p) (u p - gPu φ u p (u p))
      - gAl φ u w p • (u p - gPu φ u p (u p)) = 0 := by
    rw [h1mPu, smul_zero, map_zero, sub_zero]
  rw [gUB]
  simp only [add_apply, smul_apply, mul_apply_eq_comp, sub_apply, one_apply_eq_self]
  rw [hB0, hJ, add_zero]
  rw [gNn]
  abel

/-- Where `φ = 1`, `u p = w p ≠ 0` and `B p = 1`, the free family is `1`. -/
theorem gUB_eq_one_of_apply_eq (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (B : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (p : ℝ × ℝ) (hφp : φ p = 1) (hup : u p ≠ 0) (huw : u p = w p) (hB : B p = 1) :
    gUB φ u w B p = 1 := by
  have hAm_in : gAm φ u p = inner ℝ (u p) (u p) := by
    simp only [gAm, hφp, one_mul, sub_self, add_zero]
  have hup_ne : inner ℝ (u p) (u p) ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hup)
  have hww_ne : inner ℝ (w p) (w p) ≠ 0 := by rw [← huw]; exact hup_ne
  have hAl_one : gAl φ u w p = 1 := by
    rw [gAl, hAm_in, huw]
    exact div_self hww_ne
  have hNn_zero : gNn φ u w p = 0 := by
    rw [gNn, hAl_one, huw, one_smul, sub_self]
  have hJ_zero : gJ φ u w p = 0 := by
    rw [gJ, hNn_zero]
    simp [ContinuousLinearMap.smulRight_zero, ContinuousLinearMap.zero_smulRight]
  rw [gUB, hAl_one, hJ_zero, hB]
  simp

/-! ## Smoothness of the free family -/

/-- The free family is smooth as soon as `φ`, `u`, `w`, `B` are and `gAm φ u` is nowhere zero. -/
theorem contDiff_gUB (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m))
    (B : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (hu : ContDiff ℝ smw u) (hw : ContDiff ℝ smw w) (hB : ContDiff ℝ smw B)
    (hφ : ContDiff ℝ smw φ) (hAm : ∀ p, gAm φ u p ≠ 0) :
    ContDiff ℝ smw (fun p => gUB φ u w B p) := by
  unfold gUB
  exact (((contDiff_gAl φ u w hu hw hφ hAm).smul contDiff_const).add
    (contDiff_gJ φ u w hu hw hφ hAm)).add
    ((hB.sub ((contDiff_gAl φ u w hu hw hφ hAm).smul contDiff_const)).mul
      (contDiff_const.sub (contDiff_gPu φ u hu hφ hAm)))

/-! ## The reduction -/

/-- **The reduction of `glAuxCore` to a free corrector.**  If for every admissible `(u,w)` (smooth,
nowhere zero on the square, equal on the two edges) there is a cutoff `φ` (smooth, `1` on the
square, `gAm φ u` nowhere zero) and a smooth corrector family `B` such that

* `B` is a unit at every point of the square,
* the free family `gUB φ u w B` is a unit at every point of the square,
* `B = 1` on the two edges,

then `glAuxCore` holds: take `U := gUB φ u w B`, whose smoothness, action `U(u) = w` on the square
and triviality on the edges are proved above (`contDiff_gUB`, `gUB_apply_u`,
`gUB_eq_one_of_apply_eq`). -/
theorem glAuxCore_of_freeCorrector {m : ℕ}
    (h : ∀ (u w : ℝ → ℝ → EuclideanSpace ℝ (Fin m)),
        ContDiff ℝ smw (fun p : ℝ × ℝ => u p.1 p.2) →
        ContDiff ℝ smw (fun p : ℝ × ℝ => w p.1 p.2) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, u s t ≠ 0) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, w s t ≠ 0) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, u 0 t = w 0 t) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, u 1 t = w 1 t) →
        ∃ (φ : ℝ × ℝ → ℝ)
          (B : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)),
          ContDiff ℝ smw φ ∧
          (∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, φ p = 1) ∧
          (∀ p, gAm φ (fun q : ℝ × ℝ => u q.1 q.2) p ≠ 0) ∧
          ContDiff ℝ smw B ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (B (s, t))) ∧
          (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
            IsUnit (gUB φ (fun q : ℝ × ℝ => u q.1 q.2) (fun q : ℝ × ℝ => w q.1 q.2) B (s, t))) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1, B (0, t) = 1) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1, B (1, t) = 1)) :
    ∀ (u w : ℝ → ℝ → EuclideanSpace ℝ (Fin m)),
        ContDiff ℝ smw (fun p : ℝ × ℝ => u p.1 p.2) →
        ContDiff ℝ smw (fun p : ℝ × ℝ => w p.1 p.2) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, u s t ≠ 0) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, w s t ≠ 0) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, u 0 t = w 0 t) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, u 1 t = w 1 t) →
      ∃ U : ℝ → ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
        ContDiff ℝ smw (fun p : ℝ × ℝ => U p.1 p.2) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (U s t)) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, U s t (u s t) = w s t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, U 0 t = 1) ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, U 1 t = 1) := by
  intro u w hu hw hune hwne h0 h1
  obtain ⟨φ, B, hφsm, hφ1, hAm, hBsm, hBunit, hUunit, hB0, hB1⟩ := h u w hu hw hune hwne h0 h1
  refine ⟨fun s t => gUB φ (fun q : ℝ × ℝ => u q.1 q.2) (fun q : ℝ × ℝ => w q.1 q.2) B (s, t),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_gUB φ _ _ B hu hw hBsm hφsm hAm
  · intro s hs t ht
    exact hUunit s hs t ht
  · intro s hs t ht
    exact gUB_apply_u φ _ _ B (s, t) (hφ1 (s, t) ⟨⟨hs.1, hs.2⟩, ⟨ht.1, ht.2⟩⟩) (hune s hs t ht)
  · intro t ht
    exact gUB_eq_one_of_apply_eq φ _ _ B (0, t) (hφ1 (0, t) ⟨⟨le_rfl, zero_le_one⟩, ⟨ht.1, ht.2⟩⟩)
      (hune 0 ⟨le_rfl, zero_le_one⟩ t ht) (h0 t ht) (hB0 t ht)
  · intro t ht
    exact gUB_eq_one_of_apply_eq φ _ _ B (1, t) (hφ1 (1, t) ⟨⟨zero_le_one, le_rfl⟩, ⟨ht.1, ht.2⟩⟩)
      (hune 1 ⟨zero_le_one, le_rfl⟩ t ht) (h1 t ht) (hB1 t ht)

/-! ## The assembly: `glAuxCore` from the free-corrector input, plus the cutoff

The only remaining input is the existence of the corrector `B` for a *given* cutoff `φ`
(`exists_corrector_gUB`).  The cutoff itself is produced here by
`Work.Drive.Whitney.exists_cutoff_gAm_pos` (`gU_det_interface`), so that the caller only has to
supply the corrector statement. -/

/-- **`glAuxCore` from the corrector input.**  If for every smooth `u, w` (nowhere zero on the
square, equal on the two edges) and every cutoff `φ` (`1` on the square, `gAm φ u` nowhere zero)
there is a corrector `B` as in `exists_corrector_gUB`, then `glAuxCore` holds (for `m ≥ 2`). -/
theorem glAuxCore_of_exists_corrector_gUB {m : ℕ}
    (hcorr : ∀ (φ : ℝ × ℝ → ℝ) (u w : ℝ × ℝ → EuclideanSpace ℝ (Fin m)),
        (∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, φ p = 1) →
        (∀ p, gAm φ u p ≠ 0) →
        (∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, u p ≠ 0) →
        (∀ p ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, w p ≠ 0) →
        ContDiff ℝ smw u → ContDiff ℝ smw w →
        (∀ t ∈ Set.Icc (0:ℝ) 1, u (0, t) = w (0, t)) →
        (∀ t ∈ Set.Icc (0:ℝ) 1, u (1, t) = w (1, t)) →
        ∃ B : ℝ × ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
          ContDiff ℝ smw B ∧
          (∀ x ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, IsUnit (B x)) ∧
          (∀ x ∈ Set.Icc (0:ℝ) 1 ×ˢ Set.Icc (0:ℝ) 1, IsUnit (gUB φ u w B x)) ∧
          (∀ t ∈ Set.Icc (0:ℝ) 1, B (0, t) = 1) ∧
          (∀ t ∈ Set.Icc (0:ℝ) 1, B (1, t) = 1))
    (hm : 2 ≤ m) :
    ∀ (u w : ℝ → ℝ → EuclideanSpace ℝ (Fin m)),
        ContDiff ℝ smw (fun p : ℝ × ℝ => u p.1 p.2) →
        ContDiff ℝ smw (fun p : ℝ × ℝ => w p.1 p.2) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, u s t ≠ 0) →
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, w s t ≠ 0) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, u 0 t = w 0 t) →
        (∀ t ∈ Set.Icc (0 : ℝ) 1, u 1 t = w 1 t) →
      ∃ U : ℝ → ℝ → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m),
        ContDiff ℝ smw (fun p : ℝ × ℝ => U p.1 p.2) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (U s t)) ∧
        (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, U s t (u s t) = w s t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) 1, U 0 t = 1) ∧ (∀ t ∈ Set.Icc (0 : ℝ) 1, U 1 t = 1) := by
  intro u w hu hw hune hwne h0 h1
  -- the cutoff
  obtain ⟨φ, hφsm, -, hφ1, hAm_pos⟩ :=
    exists_cutoff_gAm_pos (fun p : ℝ × ℝ => u p.1 p.2)
      (fun p hp => hune p.1 hp.1 p.2 hp.2)
  have hAm : ∀ p : ℝ × ℝ, gAm φ (fun p : ℝ × ℝ => u p.1 p.2) p ≠ 0 :=
    fun p => ne_of_gt (hAm_pos p)
  -- the corrector for this cutoff
  obtain ⟨B, hBsm, _hBunit, hUunit, hB0, hB1⟩ :=
    hcorr φ (fun p : ℝ × ℝ => u p.1 p.2) (fun p : ℝ × ℝ => w p.1 p.2)
      hφ1 hAm
      (fun p hp => hune p.1 hp.1 p.2 hp.2)
      (fun p hp => hwne p.1 hp.1 p.2 hp.2)
      hu hw
      (fun t ht => by simpa using h0 t ht)
      (fun t ht => by simpa using h1 t ht)
  refine ⟨fun s t => gUB φ (fun q : ℝ × ℝ => u q.1 q.2) (fun q : ℝ × ℝ => w q.1 q.2) B (s, t),
    ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_gUB φ _ _ B hu hw hBsm hφsm hAm
  · intro s hs t ht
    exact hUunit (s, t) ⟨⟨hs.1, hs.2⟩, ⟨ht.1, ht.2⟩⟩
  · intro s hs t ht
    exact gUB_apply_u φ _ _ B (s, t) (hφ1 (s, t) ⟨⟨hs.1, hs.2⟩, ⟨ht.1, ht.2⟩⟩)
      (hune s hs t ht)
  · intro t ht
    exact gUB_eq_one_of_apply_eq φ _ _ B (0, t)
      (hφ1 (0, t) ⟨⟨le_rfl, zero_le_one⟩, ⟨ht.1, ht.2⟩⟩)
      (hune 0 ⟨le_rfl, zero_le_one⟩ t ht) (h0 t ht) (hB0 t ht)
  · intro t ht
    exact gUB_eq_one_of_apply_eq φ _ _ B (1, t)
      (hφ1 (1, t) ⟨⟨zero_le_one, le_rfl⟩, ⟨ht.1, ht.2⟩⟩)
      (hune 1 ⟨zero_le_one, le_rfl⟩ t ht) (h1 t ht) (hB1 t ht)

end Work.Drive.Whitney
