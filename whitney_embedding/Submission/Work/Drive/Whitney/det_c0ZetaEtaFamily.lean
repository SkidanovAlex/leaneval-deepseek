import Mathlib

namespace Work.Drive.Whitney

open scoped RealInnerProductSpace
open ContinuousLinearMap

/-- **Determinant of a map that is a scalar modulo a subspace.**
If `T x - c • x ∈ U` for all `x` (so that `T` acts as `c` on the quotient `E ⧸ U` and preserves
`U`), then `LinearMap.det T = c ^ (finrank E - finrank U) * LinearMap.det (T|_U)`. -/
lemma det_eq_pow_mul_det_restrict {E : Type*} [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E]
    (T : E →ₗ[ℝ] E) (c : ℝ) (U : Submodule ℝ E) (hle : U ≤ Submodule.comap T U)
    (hU : ∀ x, T x - c • x ∈ U) :
    LinearMap.det T = c ^ (Module.finrank ℝ E - Module.finrank ℝ U) *
      LinearMap.det (T.restrict hle) := by
  have hq : U.mapQ U T hle = c • 1 := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      rw [Submodule.mapQ_apply]
      show Submodule.Quotient.mk (T v) = Submodule.Quotient.mk (c • v)
      · rw [Submodule.Quotient.eq]
        exact hU v
  rw [LinearMap.det_eq_det_mul_det U T hle, hq, LinearMap.det_smul, map_one, mul_one]
  have hfr : Module.finrank ℝ (E ⧸ U) = Module.finrank ℝ E - Module.finrank ℝ U := by
    have h := Submodule.finrank_quotient_add_finrank U
    omega
  rw [hfr]
  ring

/-- The determinant of the `c₀`-family operator with an additional `ζ`–`η` (i.e. `z`–`e`)
rank-one part.  With `A = ‖u‖²`, `a = ⟪w,u⟫/A`, `n = w - a u`, `J` the infinitesimal generator
of the `u`-`n` rotation and `Pu` the orthogonal projection onto `ℝu`, the operator

`a • 1 + J + (C - a • 1) * (1 - Pu)`,   `C = c₀ • (1 - Pu) + (innerSL z).smulRight e`

has determinant `a c₀^(m-2) (c₀ + ⟪z,e⟫) + c₀^(m-3) ((c₀ + ⟪z,e⟫)‖n‖² - ⟪n,e⟫⟪n,z⟫)/A`.

The proof works in the (possibly dependent) spanning family `u, n, e`: the operator equals `c₀ • 1`
plus a map with image in `span{u,n,e}`, and the matrix of the latter in `Fin 3`-coordinates is
`!![a, -‖n‖²/A, -⟪n,e⟫/A; 1, c₀, 0; 0, ⟪z,n⟫, c₀ + ⟪z,e⟫]`; every relation among `u, n, e` is
an eigenvector of that matrix with eigenvalue `c₀` (because `αu + βn + γe = 0` forces `α = 0`).
This gives `det T = c₀^(m-3) det N` uniformly, without a case split. -/
theorem det_c0ZetaEtaFamily {m : ℕ} (hm : 3 ≤ m)
    (u w z e : EuclideanSpace ℝ (Fin m)) (c0 : ℝ)
    (hu : u ≠ 0) (hzu : inner ℝ z u = 0) (heu : inner ℝ e u = 0) :
    let A : ℝ := ‖u‖^2
    let a : ℝ := inner ℝ w u / A
    let n : EuclideanSpace ℝ (Fin m) := w - a • u
    let J : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
      (1/A) • ((innerSL ℝ u).smulRight n - (innerSL ℝ n).smulRight u)
    let Pu : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
      (1/A) • (innerSL ℝ u).smulRight u
    let C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
      c0 • (1 - Pu) + (innerSL ℝ z).smulRight e
    LinearMap.det ((a • 1 + J + (C - a • 1) * (1 - Pu)).toLinearMap) =
      a * c0 ^ (m - 2) * (c0 + inner ℝ z e)
        + c0 ^ (m - 3) * ((c0 + inner ℝ z e) * ‖n‖^2 - inner ℝ n e * inner ℝ n z) / A := by
  simp only []
  set A : ℝ := ‖u‖ ^ 2 with hAdef
  set a : ℝ := inner ℝ w u / A with hadef
  set nn : EuclideanSpace ℝ (Fin m) := w - a • u with hnndef
  set J : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (1/A) • ((innerSL ℝ u).smulRight nn - (innerSL ℝ nn).smulRight u) with hJdef
  set Pu : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    (1/A) • (innerSL ℝ u).smulRight u with hPudef
  set C : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    c0 • (1 - Pu) + (innerSL ℝ z).smulRight e with hCdef
  set T : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    ↑(a • 1 + J + (C - a • 1) * (1 - Pu)) with hTdef
  have hA_ne : A ≠ 0 := by rw [hAdef]; exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  have huu : ⟪u,u⟫ = A := by rw [hAdef, real_inner_self_eq_norm_sq]
  have hnn : ⟪nn,nn⟫ = ‖nn‖^2 := real_inner_self_eq_norm_sq nn
  have hnu : ⟪nn,u⟫ = 0 := by
    have h : ⟪nn, u⟫ = ⟪w, u⟫ - a * A := by
      rw [hnndef, inner_sub_left, real_inner_smul_left, huu, real_inner_comm u w]
    rw [h, hadef, div_mul_cancel₀ _ hA_ne, sub_self]
  have hun : ⟪u,nn⟫ = 0 := by rw [real_inner_comm]; exact hnu
  have huz : ⟪u,z⟫ = 0 := by rw [real_inner_comm]; exact hzu
  have hue : ⟪u,e⟫ = 0 := by rw [real_inner_comm]; exact heu
  have hJap : ∀ x, J x = (1/A) • (⟪u,x⟫ • nn - ⟪nn,x⟫ • u) := by
    intro x; rw [hJdef]; simp
  have hPuap : ∀ x, Pu x = (⟪u,x⟫ / A) • u := by
    intro x; rw [hPudef]; simp [div_eq_inv_mul, mul_comm, smul_smul]
  have h1mPu : ∀ x, (1 - Pu) x = x - (⟪u,x⟫ / A) • u := by
    intro x; rw [sub_apply, one_apply_eq_self, hPuap x]
  have hCy : ∀ y, C y = c0 • ((1 - Pu) y) + ⟪z,y⟫ • e := by
    intro y; rw [hCdef]; simp
  have hz_sub : ∀ x, ⟪z, (1 - Pu) x⟫ = ⟪z, x⟫ := by
    intro x; rw [h1mPu x, inner_sub_right, real_inner_smul_right, hzu]; ring
  have hu_sub : ∀ x, ⟪u, (1 - Pu) x⟫ = 0 := by
    intro x; rw [h1mPu x, inner_sub_right, real_inner_smul_right, huu,
      div_mul_cancel₀ _ hA_ne, sub_self]
  have hTapply : ∀ x, T x = a • x + J x + (C - a • 1) ((1 - Pu) x) := by
    intro x; rw [hTdef]; simp
  -- the explicit form of `T`
  have hkey : ∀ x, T x = c0 • x + (⟪u,x⟫/A) • nn - ((⟪nn,x⟫ + (c0-a)*⟪u,x⟫)/A) • u
      + ⟪z,x⟫ • e := by
    intro x
    have hPP : (1 - Pu) ((1 - Pu) x) = (1 - Pu) x := by
      rw [h1mPu ((1 - Pu) x), hu_sub x]; simp
    rw [hTapply x, hJap x, sub_apply, hCy ((1 - Pu) x), hPP, hz_sub x, h1mPu x]
    simp only [smul_sub, smul_apply, one_apply_eq_self]
    module
  have hTu : T u = a • u + nn := by
    rw [hkey u, huu, hnu, hzu]
    simp only [zero_smul, add_zero]
    have h1 : A / A = 1 := div_self hA_ne
    have h2 : (0 + (c0 - a) * A) / A = c0 - a := by field_simp; ring
    rw [h1, h2]
    simp only [one_smul]
    module
  have hTnn : T nn = (-(‖nn‖^2/A)) • u + c0 • nn + ⟪z,nn⟫ • e := by
    rw [hkey nn, hun, hnn]
    simp only [mul_zero, zero_div, zero_smul, add_zero]
    module
  have hTe : T e = (-(⟪nn,e⟫/A)) • u + (c0 + ⟪z,e⟫) • e := by
    rw [hkey e, hue]
    simp only [mul_zero, zero_div, zero_smul, add_zero]
    module
  -- the spanning family and the coordinate matrix
  let V : Fin 3 → EuclideanSpace ℝ (Fin m) := ![u, nn, e]
  let Ψ : (Fin 3 → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) := Fintype.linearCombination ℝ V
  set Nmat : Matrix (Fin 3) (Fin 3) ℝ :=
    !![a, -(‖nn‖^2/A), -(⟪nn,e⟫/A); 1, c0, 0; 0, ⟪z,nn⟫, c0+⟪z,e⟫] with hNmatdef
  let N : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) := Matrix.toLin' Nmat
  have hΨ_apply : ∀ v : Fin 3 → ℝ, Ψ v = ∑ i, v i • V i :=
    fun v => Fintype.linearCombination_apply ℝ V v
  have hΨsingle : ∀ j : Fin 3, Ψ (Pi.single j (1:ℝ)) = V j := by
    intro j
    rw [hΨ_apply, Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro h; simp at h
  have hV0 : V (0:Fin 3) = u := rfl
  have hV1 : V (1:Fin 3) = nn := rfl
  have hV2 : V (2:Fin 3) = e := rfl
  have hcol0 : N (Pi.single (0:Fin 3) (1:ℝ)) = ![a, (1:ℝ), 0] := by
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    ext i
    fin_cases i <;> simp [Matrix.col_apply, hNmatdef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hcol1 : N (Pi.single (1:Fin 3) (1:ℝ)) = ![-(‖nn‖^2/A), c0, ⟪z,nn⟫] := by
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    ext i
    fin_cases i <;> simp [Matrix.col_apply, hNmatdef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hcol2 : N (Pi.single (2:Fin 3) (1:ℝ)) = ![-(⟪nn,e⟫/A), (0:ℝ), c0 + ⟪z,e⟫] := by
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
    ext i
    fin_cases i <;> simp [Matrix.col_apply, hNmatdef, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  -- the intertwining relation `T ∘ Ψ = Ψ ∘ N`
  have hTΨ0 : T (Ψ (Pi.single (0:Fin 3) (1:ℝ))) = Ψ (N (Pi.single (0:Fin 3) (1:ℝ))) := by
    rw [hΨsingle, hcol0, hV0, hTu, hΨ_apply, Fin.sum_univ_three]
    simp [V, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  have hTΨ1 : T (Ψ (Pi.single (1:Fin 3) (1:ℝ))) = Ψ (N (Pi.single (1:Fin 3) (1:ℝ))) := by
    rw [hΨsingle, hcol1, hV1, hTnn, hΨ_apply, Fin.sum_univ_three]
    simp [V, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  have hTΨ2 : T (Ψ (Pi.single (2:Fin 3) (1:ℝ))) = Ψ (N (Pi.single (2:Fin 3) (1:ℝ))) := by
    rw [hΨsingle, hcol2, hV2, hTe, hΨ_apply, Fin.sum_univ_three]
    simp [V, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  have hTΨ : ∀ j : Fin 3, T (Ψ (Pi.single j (1:ℝ))) = Ψ (N (Pi.single j (1:ℝ))) := by
    intro j
    fin_cases j
    · simpa using hTΨ0
    · simpa using hTΨ1
    · simpa using hTΨ2
  have hfac : T ∘ₗ Ψ = Ψ ∘ₗ N := by
    refine (Pi.basisFun ℝ (Fin 3)).ext (fun j => ?_)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Pi.basisFun_apply]
    exact hTΨ j
  have hfac_apply : ∀ v, T (Ψ v) = Ψ (N v) := fun v => LinearMap.congr_fun hfac v
  have hle : Ψ.range ≤ (Ψ.range).comap T := by
    rintro x ⟨v, rfl⟩
    exact ⟨N v, (hfac_apply v).symm⟩
  have hrange : ∀ x, T x - c0 • x ∈ Ψ.range := by
    intro x
    refine ⟨![-(⟪nn,x⟫ + (c0-a)*⟪u,x⟫)/A, ⟪u,x⟫/A, ⟪z,x⟫], ?_⟩
    rw [hΨ_apply, Fin.sum_univ_three]
    simp only [V, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    rw [hkey x]
    module
  -- every relation among `u, nn, e` is a `c0`-eigenvector of `N`
  have hker : ∀ v ∈ Ψ.ker, N v = c0 • v := by
    intro v hv
    rw [LinearMap.mem_ker] at hv
    have hrel : v 0 • u + v 1 • nn + v 2 • e = 0 := by
      have h := hΨ_apply v
      rw [h, Fin.sum_univ_three] at hv
      simpa [V, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons] using hv
    have hv0 : v 0 = 0 := by
      have h := congrArg (fun y => ⟪u, y⟫) hrel
      simp only [inner_add_right, inner_zero_right, real_inner_smul_right, huu, hun, hue, mul_zero,
        add_zero] at h
      exact (mul_eq_zero.mp h).resolve_right hA_ne
    have hrel2 : v 1 • nn + v 2 • e = 0 := by simpa [hv0] using hrel
    have hv1 : v 1 * ‖nn‖^2 + v 2 * ⟪nn,e⟫ = 0 := by
      have h := congrArg (fun y => ⟪nn, y⟫) hrel2
      simpa only [inner_add_right, inner_zero_right, real_inner_smul_right, hnn, mul_zero,
        add_zero] using h
    have hv2 : v 1 * ⟪z,nn⟫ + v 2 * ⟪z,e⟫ = 0 := by
      have h := congrArg (fun y => ⟪z, y⟫) hrel2
      simpa only [inner_add_right, inner_zero_right, real_inner_smul_right, mul_zero,
        add_zero] using h
    have hvsum : v = ∑ i, v i • Pi.single i (1:ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have hexp : N v = v 0 • N (Pi.single (0:Fin 3) (1:ℝ)) + v 1 • N (Pi.single (1:Fin 3) (1:ℝ))
        + v 2 • N (Pi.single (2:Fin 3) (1:ℝ)) := by
      conv_lhs => rw [hvsum]
      rw [map_sum, Fin.sum_univ_three, map_smul, map_smul, map_smul]
    rw [hexp, hcol0, hcol1, hcol2]
    ext i
    fin_cases i <;> simp [Pi.add_apply, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, smul_eq_mul]
    · linear_combination (a - c0) * hv0 + (-1/A) * hv1
    · linear_combination hv0
    · linear_combination hv2
  -- determinant assembly
  have hdT : LinearMap.det T = c0 ^ (m - Module.finrank ℝ Ψ.range) *
      LinearMap.det (T.restrict hle) := by
    rw [det_eq_pow_mul_det_restrict T c0 Ψ.range hle hrange, finrank_euclideanSpace,
      Fintype.card_fin]
  have hNle : Ψ.ker ≤ (Ψ.ker).comap N := fun v hv => by
    rw [Submodule.mem_comap, hker v hv]
    exact Submodule.smul_mem _ _ hv
  have hresN : LinearMap.det (N.restrict hNle) = c0 ^ Module.finrank ℝ Ψ.ker := by
    have hid : (N.restrict hNle : ↥Ψ.ker →ₗ[ℝ] ↥Ψ.ker) = c0 • 1 := by
      refine LinearMap.ext fun v => ?_
      rw [LinearMap.restrict_apply, LinearMap.smul_apply]
      refine Subtype.ext ?_
      simpa using hker v v.2
    rw [hid, LinearMap.det_smul, map_one, mul_one]
  set φ : ((Fin 3 → ℝ) ⧸ Ψ.ker) ≃ₗ[ℝ] Ψ.range := Ψ.quotKerEquivRange with hφdef
  have hsymm : ∀ v : Fin 3 → ℝ, φ.symm ⟨Ψ v, LinearMap.mem_range_self Ψ v⟩ =
      Submodule.Quotient.mk v := by
    intro v
    rw [← Submodule.mkQ_apply, hφdef]
    exact LinearMap.quotKerEquivRange_symm_apply_image Ψ v (LinearMap.mem_range_self Ψ v)
  have hφ_apply : ∀ v : Fin 3 → ℝ, φ (Submodule.Quotient.mk v) =
      ⟨Ψ v, LinearMap.mem_range_self Ψ v⟩ := by
    intro v
    rw [← hsymm v, LinearEquiv.apply_symm_apply]
  have hconj : (↑φ ∘ₗ Ψ.ker.mapQ Ψ.ker N hNle ∘ₗ ↑φ.symm) =
      (T.restrict hle : ↥Ψ.range →ₗ[ℝ] ↥Ψ.range) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨v, hv⟩ := x.2
    have hx : x = ⟨Ψ v, LinearMap.mem_range_self Ψ v⟩ := Subtype.ext hv.symm
    rw [hx]
    refine Subtype.ext ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hsymm v, Submodule.mapQ_apply, hφ_apply (N v), LinearMap.coe_restrict_apply]
    exact (hfac_apply v).symm
  have hmapQdet : LinearMap.det (T.restrict hle) =
      LinearMap.det (Ψ.ker.mapQ Ψ.ker N hNle) := by
    rw [← hconj, LinearMap.det_conj]
  have hdetN : LinearMap.det N = c0 ^ Module.finrank ℝ Ψ.ker *
      LinearMap.det (T.restrict hle) := by
    rw [LinearMap.det_eq_det_mul_det Ψ.ker N hNle, hresN, ← hmapQdet]
  have hexp3 : m - 3 + Module.finrank ℝ Ψ.ker = m - Module.finrank ℝ Ψ.range := by
    have h := LinearMap.finrank_range_add_finrank_ker Ψ
    rw [Module.finrank_fin_fun] at h
    omega
  have hmain : LinearMap.det T = c0 ^ (m - 3) * LinearMap.det N := by
    rw [hdT, hdetN, ← mul_assoc, ← pow_add, hexp3]
  rw [hmain, LinearMap.det_toLin', Matrix.det_fin_three]
  simp only [hNmatdef, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hp2 : c0 ^ (m - 2) = c0 ^ (m - 3) * c0 := by
    rw [← pow_succ]; congr 1; omega
  rw [hp2, real_inner_comm nn z]
  ring

end Work.Drive.Whitney
