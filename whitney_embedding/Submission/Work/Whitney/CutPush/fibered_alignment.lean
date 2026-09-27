import Mathlib

/-!
# The fibered alignment of a family of equivalences

`Work.Whitney.CutPush.exists_fibered_alignment` (`CutPush/NOTES_STATE_S59.md` §1.1, §6.2): given a
smooth family `M s` of linear equivalences of `ℝ^m` fixing a vector `e ≠ 0` and preserving its
orthogonal complement `eᗮ` (both clauses are what the ODE transport of `CutPush/frame_ode.lean`
provides, see `CutPush/frame_transport_perp.lean`), the map

    A y  =  a + M (ζ y) (y - a),      ζ y = ⟪y - a, e⟫ / ⟪e, e⟫

is a global `C^∞` diffeomorphism of `ℝ^m`, it fixes every point of the affine line `a + ℝe`, and its
derivative there is exactly the prescribed family: `dA (a + s e) = M s`.

`A` is the *fibered* map `(s, u) ↦ (s, M s u)` in the coordinates
`ℝ^m = ℝe ⊕ eᗮ`; its inverse is

    B z  =  a + ζ z • e + (M (ζ z))⁻¹ (z - a - ζ z • e).

The two clauses `M s e = e` and `M s u ⊥ e` for `u ⊥ e` are exactly what makes both `ζ` and the
`e`-coordinate of the fibers invariant, hence what makes `A` invertible; they also make the
`e`-component of the derivative of `A` at `a + s e` cancel, giving `dA (a + s e) = M s`.
-/

namespace Work.Whitney.CutPush

open scoped Topology ContDiff
open Function

/-- **The fibered alignment.** -/
theorem exists_fibered_alignment {m : ℕ}
    (M : ℝ → EuclideanSpace ℝ (Fin m) ≃L[ℝ] EuclideanSpace ℝ (Fin m))
    (hM : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => M p.1 p.2))
    (hMi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin m) => (M p.1).symm p.2))
    (a e : EuclideanSpace ℝ (Fin m)) (he : e ≠ 0)
    (hMe : ∀ s : ℝ, M s e = e)
    (hMperp : ∀ s : ℝ, ∀ u : EuclideanSpace ℝ (Fin m),
      inner ℝ u e = 0 → inner ℝ (M s u) e = 0) :
    ∃ (A Ainv : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ainv ∧
      Function.LeftInverse Ainv A ∧ Function.RightInverse Ainv A ∧
      (∀ s : ℝ, A (a + s • e) = a + s • e) ∧
      (∀ s : ℝ, ∀ v : EuclideanSpace ℝ (Fin m),
        fderiv ℝ A (a + s • e) v = M s v) := by
  classical
  have hcpos : 0 < inner ℝ e e := real_inner_self_pos.mpr he
  have hcne : inner ℝ e e ≠ 0 := ne_of_gt hcpos
  set ζ : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun y => inner ℝ e (y - a) / inner ℝ e e with hζ
  set A : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun y => a + M (ζ y) (y - a) with hA
  set B : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun z => a + ζ z • e + (M (ζ z)).symm (z - a - ζ z • e) with hB
  have hζmul : ∀ y : EuclideanSpace ℝ (Fin m), ζ y * inner ℝ e e = inner ℝ e (y - a) := by
    intro y
    simp only [hζ]
    exact div_mul_cancel₀ _ hcne
  have hζsmul : ∀ s : ℝ, ζ (a + s • e) = s := by
    intro s
    have h1 : (a + s • e) - a = s • e := by abel
    show inner ℝ e ((a + s • e) - a) / inner ℝ e e = s
    rw [h1, real_inner_smul_right]
    exact mul_div_cancel_right₀ s hcne
  have hperp_split : ∀ y : EuclideanSpace ℝ (Fin m), inner ℝ e (y - a - ζ y • e) = 0 := by
    intro y
    rw [inner_sub_right, real_inner_smul_right, hζmul y, sub_self]
  have hperp_split' : ∀ y : EuclideanSpace ℝ (Fin m),
      inner ℝ (y - a - ζ y • e) e = 0 := by
    intro y
    rw [real_inner_comm]
    exact hperp_split y
  have hMperp_inv : ∀ s : ℝ, ∀ u : EuclideanSpace ℝ (Fin m),
      inner ℝ u e = 0 → inner ℝ ((M s).symm u) e = 0 := by
    intro s u hu
    set w : EuclideanSpace ℝ (Fin m) := (M s).symm u with hw
    set t : ℝ := inner ℝ w e / inner ℝ e e with ht
    have htw : inner ℝ (w - t • e) e = 0 := by
      have h1 : t * inner ℝ e e = inner ℝ w e := by
        simp only [ht]
        exact div_mul_cancel₀ _ hcne
      rw [inner_sub_left, real_inner_smul_left, h1, sub_self]
    have hMw : M s (t • e + (w - t • e)) = u := by
      have h1 : t • e + (w - t • e) = w := by abel
      rw [h1, hw]
      exact ContinuousLinearEquiv.apply_symm_apply (M s) u
    have hsplit : u = t • e + M s (w - t • e) := by
      rw [← hMw, map_add, map_smul, hMe]
    have hzero : t * inner ℝ e e = 0 := by
      have h2 := hu
      rw [hsplit, inner_add_left, real_inner_smul_left, hMperp s (w - t • e) htw,
        add_zero] at h2
      exact h2
    have ht0 : t = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact h
      · exact absurd h hcne
    have h3 : w - t • e = w := by rw [ht0, zero_smul, sub_zero]
    rw [← h3]
    exact htw
  set N : ℝ → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) :=
    fun s => (M s : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) with hN
  have hNcur : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) N := by
    rw [contDiff_clm_apply_iff]
    intro y
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => (x, y)) :=
      ContDiff.prodMk contDiff_id contDiff_const
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => M x y) := hM.comp h2
    simpa [hN] using h3
  have hMFix : ∀ s : ℝ, ∀ δ : ℝ, (fderiv ℝ N s δ) e = 0 := by
    intro s δ
    have hderiv : HasFDerivAt N (fderiv ℝ N s) s :=
      ((hNcur.differentiable (by simp)) s).hasFDerivAt
    have h1 : HasFDerivAt (fun x : ℝ => M x e) (((fderiv ℝ N s).flip e)) s := by
      have h0 : HasFDerivAt (fun x : ℝ => N x e)
          (N s ∘SL (0 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin m)) + (fderiv ℝ N s).flip e) s :=
        hderiv.clm_apply (hasFDerivAt_const e s)
      have h0' : HasFDerivAt (fun x : ℝ => N x e) (((fderiv ℝ N s).flip e)) s := by
        simpa using h0
      simpa [hN] using h0'
    have h2 : HasFDerivAt (fun x : ℝ => M x e) (0 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin m)) s := by
      have hfun : (fun x : ℝ => M x e) = fun _ : ℝ => e := funext (fun x => hMe x)
      rw [hfun]
      exact hasFDerivAt_const e s
    have h3 := h1.unique h2
    have h4 : ((fderiv ℝ N s).flip e) δ = (0 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin m)) δ := by
      rw [h3]
    simpa using h4
  have hMdecomp : ∀ s : ℝ, ∀ y : EuclideanSpace ℝ (Fin m),
      M s (y - a) = ζ y • e + M s (y - a - ζ y • e) := by
    intro s y
    have h1 : y - a = ζ y • e + (y - a - ζ y • e) := by abel
    calc M s (y - a) = M s (ζ y • e + (y - a - ζ y • e)) := by rw [← h1]
      _ = M s (ζ y • e) + M s (y - a - ζ y • e) := by rw [map_add]
      _ = ζ y • (M s e) + M s (y - a - ζ y • e) := by rw [map_smul]
      _ = ζ y • e + M s (y - a - ζ y • e) := by rw [hMe]
  have hAy_eq : ∀ y : EuclideanSpace ℝ (Fin m), A y - a = M (ζ y) (y - a) := by
    intro y
    show a + M (ζ y) (y - a) - a = M (ζ y) (y - a)
    abel
  have hBz_eq : ∀ z : EuclideanSpace ℝ (Fin m),
      B z - a = ζ z • e + (M (ζ z)).symm (z - a - ζ z • e) := by
    intro z
    show a + ζ z • e + (M (ζ z)).symm (z - a - ζ z • e) - a
      = ζ z • e + (M (ζ z)).symm (z - a - ζ z • e)
    abel
  have hinnerAy : ∀ y : EuclideanSpace ℝ (Fin m),
      inner ℝ e (A y - a) = ζ y * inner ℝ e e := by
    intro y
    rw [hAy_eq y, hMdecomp (ζ y) y, inner_add_right, real_inner_smul_right]
    have h0 : inner ℝ e (M (ζ y) (y - a - ζ y • e)) = 0 := by
      rw [real_inner_comm]
      exact hMperp (ζ y) (y - a - ζ y • e) (hperp_split' y)
    rw [h0, add_zero]
  have hζA : ∀ y : EuclideanSpace ℝ (Fin m), ζ (A y) = ζ y := by
    intro y
    have hgoal : inner ℝ e (A y - a) / inner ℝ e e = inner ℝ e (y - a) / inner ℝ e e := by
      rw [hinnerAy y, hζmul y]
    simpa only [hζ] using hgoal
  have hinnerBz : ∀ z : EuclideanSpace ℝ (Fin m),
      inner ℝ e (B z - a) = ζ z * inner ℝ e e := by
    intro z
    rw [hBz_eq z, inner_add_right, real_inner_smul_right]
    have h0 : inner ℝ e ((M (ζ z)).symm (z - a - ζ z • e)) = 0 := by
      rw [real_inner_comm]
      exact hMperp_inv (ζ z) (z - a - ζ z • e) (hperp_split' z)
    rw [h0, add_zero]
  have hζB : ∀ z : EuclideanSpace ℝ (Fin m), ζ (B z) = ζ z := by
    intro z
    have hgoal : inner ℝ e (B z - a) / inner ℝ e e = inner ℝ e (z - a) / inner ℝ e e := by
      rw [hinnerBz z, hζmul z]
    simpa only [hζ] using hgoal
  have hAB : ∀ y : EuclideanSpace ℝ (Fin m), B (A y) = y := by
    intro y
    have harg : A y - a - ζ (A y) • e = M (ζ y) (y - a - ζ y • e) := by
      have h2 : M (ζ y) (ζ y • e) = ζ y • e := by rw [map_smul, hMe]
      calc A y - a - ζ (A y) • e = M (ζ y) (y - a) - ζ y • e := by rw [hAy_eq y, hζA y]
        _ = M (ζ y) (y - a) - M (ζ y) (ζ y • e) := by rw [h2]
        _ = M (ζ y) (y - a - ζ y • e) := by rw [← map_sub]
    show a + ζ (A y) • e + (M (ζ (A y))).symm (A y - a - ζ (A y) • e) = y
    rw [harg, hζA y, ContinuousLinearEquiv.symm_apply_apply]
    abel
  have hBA : ∀ z : EuclideanSpace ℝ (Fin m), A (B z) = z := by
    intro z
    show a + M (ζ (B z)) (B z - a) = z
    rw [hζB z, hBz_eq z, map_add]
    have h2 : M (ζ z) (ζ z • e) = ζ z • e := by rw [map_smul, hMe]
    rw [h2, ContinuousLinearEquiv.apply_symm_apply]
    abel
  have hcontζ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w : EuclideanSpace ℝ (Fin m) => inner ℝ e w) := (innerSL ℝ e).contDiff
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin m) => inner ℝ e (y - a)) :=
      h1.comp (contDiff_id.sub contDiff_const)
    have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin m) => inner ℝ e (y - a) / inner ℝ e e) :=
      h2.div_const _
    simpa only [hζ] using h4
  have hAcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin m) => (ζ y, y - a)) :=
      ContDiff.prodMk hcontζ (contDiff_id.sub contDiff_const)
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin m) => M (ζ y) (y - a)) := hM.comp h1
    have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin m) => a + M (ζ y) (y - a)) :=
      contDiff_const.add h3
    simpa only [hA] using h4
  have hBcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B := by
    have h0 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin m) => z - a - ζ z • e) :=
      (contDiff_id.sub contDiff_const).sub (hcontζ.smul contDiff_const)
    have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin m) => (ζ z, z - a - ζ z • e)) :=
      ContDiff.prodMk hcontζ h0
    have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin m) => (M (ζ z)).symm (z - a - ζ z • e)) := hMi.comp h1
    have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : EuclideanSpace ℝ (Fin m) => a + ζ z • e + (M (ζ z)).symm (z - a - ζ z • e)) :=
      (contDiff_const.add (hcontζ.smul contDiff_const)).add h3
    simpa only [hB] using h4
  refine ⟨A, B, hAcont, hBcont, hAB, hBA, ?_, ?_⟩
  · intro s
    show a + M (ζ (a + s • e)) ((a + s • e) - a) = a + s • e
    rw [hζsmul s]
    have h1 : (a + s • e) - a = s • e := by abel
    rw [h1, map_smul, hMe]
  · intro s v
    have hdiff : (a + s • e) - a = s • e := by abel
    set Ψc : (ℝ × EuclideanSpace ℝ (Fin m)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
      (N (ζ (a + s • e))).comp (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))
        + (((fderiv ℝ N (ζ (a + s • e))).comp
            (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m)))).flip ((a + s • e) - a))
      with hΨc
    set φc : EuclideanSpace ℝ (Fin m) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin m)) :=
      (fderiv ℝ ζ (a + s • e)).prod
        (1 : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m)) with hφc
    have hNd : HasFDerivAt N (fderiv ℝ N (ζ (a + s • e))) (ζ (a + s • e)) :=
      ((hNcur.differentiable (by simp)) (ζ (a + s • e))).hasFDerivAt
    have hζd : HasFDerivAt ζ (fderiv ℝ ζ (a + s • e)) (a + s • e) :=
      ((hcontζ.differentiable (by simp)) (a + s • e)).hasFDerivAt
    have hφd : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin m) => (ζ y, y - a)) φc (a + s • e) :=
      hζd.prodMk ((hasFDerivAt_id (a + s • e)).sub_const a)
    have hfst' : HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ (Fin m) => p.1)
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m)))
        ((ζ (a + s • e)), (a + s • e) - a) := hasFDerivAt_fst
    have hcfst := HasFDerivAt.comp ((ζ (a + s • e)), (a + s • e) - a) hNd hfst'
    have hud : HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ (Fin m) => p.2)
        (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))
        ((ζ (a + s • e)), (a + s • e) - a) := hasFDerivAt_snd
    have hΨd : HasFDerivAt (fun p : ℝ × EuclideanSpace ℝ (Fin m) => M p.1 p.2) Ψc
        ((ζ (a + s • e)), (a + s • e) - a) := by
      rw [hΨc]
      exact hcfst.clm_apply hud
    have hcomp := hΨd.comp (a + s • e) hφd
    have hAc : HasFDerivAt A (Ψc ∘SL φc) (a + s • e) := by
      have h1 : (fun y : EuclideanSpace ℝ (Fin m) => a + M (ζ y) (y - a)) = A := by rw [hA]
      rw [← h1]
      exact hcomp.const_add a
    rw [hAc.fderiv, ContinuousLinearMap.comp_apply]
    have hφv : φc v = (fderiv ℝ ζ (a + s • e) v, v) := by
      rw [hφc]
      simp only [ContinuousLinearMap.prod_apply, ContinuousLinearMap.one_apply]
    rw [hφv, hΨc]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
    rw [hζsmul s, hdiff, map_smul]
    have hp1 : (ContinuousLinearMap.snd ℝ ℝ (EuclideanSpace ℝ (Fin m)))
        ((fderiv ℝ ζ (a + s • e)) v, v) = v := rfl
    have hp2 : (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin m)))
        ((fderiv ℝ ζ (a + s • e)) v, v) = (fderiv ℝ ζ (a + s • e)) v := rfl
    rw [hp1, hp2, hMFix s (fderiv ℝ ζ (a + s • e) v), smul_zero, add_zero]
    rfl

end Work.Whitney.CutPush
