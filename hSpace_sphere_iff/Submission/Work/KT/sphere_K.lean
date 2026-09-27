import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.SphereSetup
import Submission.Work.KT.SphereAux
import Submission.Work.KT.diskQuot
import Submission.Work.KT.ball_K
import Submission.Work.KT.psi_exists
import Submission.Work.KT.k0_basic
import Submission.Work.KT.K0_prod
import Submission.Work.KT.BallKAsm
import Submission.Work.KT.sphere_K_even

/-!
# `K̃(S^d)` for the unit sphere of a finite-dimensional real normed space

Node `sphere_K` of the Adams–Atiyah development: the reduced `K`-group of the unit sphere of a
`(d+1)`-dimensional real normed space is infinite cyclic with `ψ^k = k^j` when `d = 2j`, and
vanishes when `d` is odd.

The proof transports the computation of `K̃(D_V/S_V) = K̃(S^d)` (`ball_K`) across the algebra
isomorphism `C(Sph V) ≅ Kpair (ℝ^d)`, built here from the standard quotient map `D^d → S^d`
(`sphKT_exists_algEquiv_Kpair`, from `SphereAux`/`diskQuot`).

## Where the two clauses of the statement come from

* `finrank ℝ V = 2 * j + 1` (i.e. the sphere `S^{2j}`): the *even-dimensional* case of `ball_K`
  — infinite cyclic reduced group with `ψ² = 2^j`, `ψ³ = 3^j` on it.  It is taken from
  `Work.KT.sphKT_ball_K` (`Submission/Work/KT/BallKAsm.lean`), the assembly of
  `ball_K_of` from the four ingredient nodes `ballK_transfer`, `SG.kpair_R_vanishing`,
  `ballK_dim2`, `ballK_step`.  (`BallKAsm.lean` performs the fifteen-line assembly of
  `NOTES_ext_generator.md` §5(b) itself, so that this node does not depend on the still
  `sorry`-ed final line of `ball_K.lean`, nor on `ballK_dim1.lean`, which currently misses an
  import and does not compile.)
* `finrank ℝ V = 2 * j + 2` (i.e. the sphere `S^{2j+1}`): the *odd-dimensional* case,
  `K̃ = 0`.  It is taken from `Work.KT.sphere_K_even` (`Submission/Work/KT/sphere_K_even.lean`),
  the transport of `Work.KT.SG.oddKpair_vanishing` — a route through the Bott suspension that
  needs no Adams operation at all.

Both routes rest on `Work.KT.fund_product` (Bott periodicity) and on nothing else that is still
`sorry`-ed, so `sphere_K` becomes `sorry`-free exactly when `fund_product` does.

The auxiliary module `Submission/Work/KT/K0Shim.lean` supplies the elementary `K₀` lemmas that
`Work.KT.K0_prod` needs, under clash-free names, so that `K0_prod` no longer has to import
`Fund.Basic` — the ψ-chain and the Bott/Fund-chain had two duplicate declarations
(`Work.KT.K0.map_cls`, `Work.KT.reindex_one'`).
-/

namespace Work.KT

noncomputable section

open Matrix

set_option maxHeartbeats 800000

/-! ## `K₀` along algebra isomorphisms -/

section Transport

variable {A B C : Type} [Ring A] [Ring B] [Ring C] [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C]

lemma sphKT_K0.mapA_comp (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) :
    K0.mapA (ψ.comp φ) = (K0.mapA ψ).comp (K0.mapA φ) := by
  have hto : (ψ.comp φ).toRingHom = ψ.toRingHom.comp φ.toRingHom := by ext x; rfl
  change K0.map (ψ.comp φ).toRingHom = (K0.map ψ.toRingHom).comp (K0.map φ.toRingHom)
  rw [hto]
  exact k0_basic.2.2.1 (A := A) (B := B) (C := C) φ.toRingHom ψ.toRingHom

lemma sphKT_K0.mapA_id : K0.mapA (AlgHom.id ℂ A) = AddMonoidHom.id (K0 A) :=
  k0_basic.2.2.2.1 (A := A)

lemma sphKT_K0.mapA_symm_apply (Φ : A ≃ₐ[ℂ] B) (x : K0 A) :
    K0.mapA (Φ.symm).toAlgHom (K0.mapA Φ.toAlgHom x) = x := by
  have h2 : (K0.mapA (Φ.symm).toAlgHom).comp (K0.mapA Φ.toAlgHom) =
      AddMonoidHom.id (K0 A) := by
    rw [← sphKT_K0.mapA_comp Φ.toAlgHom (Φ.symm).toAlgHom, AlgEquiv.symm_comp (e := Φ)]
    exact sphKT_K0.mapA_id
  exact congrFun (congrArg DFunLike.coe h2) x

lemma sphKT_K0.mapA_apply_symm (Φ : A ≃ₐ[ℂ] B) (x : K0 B) :
    K0.mapA Φ.toAlgHom (K0.mapA (Φ.symm).toAlgHom x) = x := by
  have h2 : (K0.mapA Φ.toAlgHom).comp (K0.mapA (Φ.symm).toAlgHom) =
      AddMonoidHom.id (K0 B) := by
    rw [← sphKT_K0.mapA_comp (Φ.symm).toAlgHom Φ.toAlgHom, AlgEquiv.comp_symm (e := Φ)]
    exact sphKT_K0.mapA_id
  exact congrFun (congrArg DFunLike.coe h2) x

lemma sphKT_K0.mapA_injective (Φ : A ≃ₐ[ℂ] B) : Function.Injective (K0.mapA Φ.toAlgHom) := by
  intro x y h
  rw [← sphKT_K0.mapA_symm_apply Φ x, ← sphKT_K0.mapA_symm_apply Φ y, h]

end Transport

/-! ## The ring isomorphism `C(Sph V) ≅ Kpair ℝ^d` -/

section RingIso

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The algebra isomorphism `C(Sph V) ≅ Kpair (ℝ^d)` when `finrank ℝ V = d + 1`, compatible with
the augmentations: evaluation at `t0` corresponds to evaluation at any boundary point. -/
lemma sphKT_exists_algEquiv_Kpair (t0 : Sph V) (d : ℕ) (hd1 : 1 ≤ d)
    (hd : Module.finrank ℝ V = d + 1) :
    ∃ Φ : C(Sph V, ℂ) ≃ₐ[ℂ] Kpair (Euc d),
      ∀ (y0 : Ball (Euc d)) (hy0 : y0 ∈ bdry (Euc d)), ∀ h : C(Sph V, ℂ),
        augPair (Euc d) y0 (Φ h) = evalC t0 h := by
  obtain ⟨e, he⟩ := sphKT_exists_sphereHomeo_modelSphere V t0 d hd
  obtain ⟨q, hq, hnp, hfib⟩ := diskQuot d hd1
  let hf : ∀ x x' : Ball (Euc d), q x = q x' →
      x = x' ∨ (x ∈ bdry (Euc d) ∧ x' ∈ bdry (Euc d)) := fun x x' h => (hfib x x').mp h
  let Ψ : C(Sph (ModelSphere d), ℂ) ≃ₐ[ℂ] Kpair (Euc d) := sphKT_diskQuotAlgEquiv d q hq hf hnp
  refine ⟨(sphKT_pullAlgEquiv e.symm).trans Ψ, ?_⟩
  intro y0 hy0 h
  rw [AlgEquiv.trans_apply]
  have hΨ : augPair (Euc d) y0 (Ψ ((sphKT_pullAlgEquiv e.symm) h))
      = evalC (sphKT_northPole d) ((sphKT_pullAlgEquiv e.symm) h) :=
    diskQuotAlgEquiv_aug d q hq hf hnp y0 hy0 _
  rw [hΨ]
  have hsymm : e.symm (sphKT_northPole d) = t0 := by rw [← he, Homeomorph.symm_apply_apply]
  change ((sphKT_pullAlgEquiv e.symm) h) (sphKT_northPole d) = h t0
  rw [pullAlgEquiv_apply_apply, hsymm]

end RingIso

lemma sphKT_exists_unit_Euc (d : ℕ) (hd : 1 ≤ d) :
    ∃ y0 : Ball (Euc d), y0 ∈ bdry (Euc d) := by
  refine ⟨⟨EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ), ?_⟩, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, PiLp.norm_single, norm_one]
  · show ‖(EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) : Euc d)‖ = 1
    rw [PiLp.norm_single, norm_one]

section Main

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma sphere_K_odd_aux (t0 : Sph V) (j : ℕ) (hj : 1 ≤ j)
    (hV : Module.finrank ℝ V = 2 * j + 1) :
    (∃ g : K0 C(Sph V, ℂ), K0.mapA (evalC t0) g = 0 ∧ (∀ k : ℤ, k • g = 0 → k = 0) ∧
        ∀ z, K0.mapA (evalC t0) z = 0 → ∃ k : ℤ, z = k • g) ∧
    (∀ ψ : K0 C(Sph V, ℂ) →+ K0 C(Sph V, ℂ), IsPsi2 ψ →
        ∀ z, K0.mapA (evalC t0) z = 0 → ψ z = (2 ^ j : ℤ) • z) ∧
    (∀ ψ : K0 C(Sph V, ℂ) →+ K0 C(Sph V, ℂ), IsPsi3 ψ →
        ∀ z, K0.mapA (evalC t0) z = 0 → ψ z = (3 ^ j : ℤ) • z) := by
  have hd1 : 1 ≤ 2 * j := by omega
  obtain ⟨Φ, hΦ⟩ := sphKT_exists_algEquiv_Kpair V t0 (2 * j) hd1 (by omega)
  obtain ⟨y0, hy0⟩ := sphKT_exists_unit_Euc (2 * j) hd1
  have hχ : K0.mapA (evalC t0) =
      (K0.mapA (augPair (Euc (2 * j)) y0)).comp (K0.mapA Φ.toAlgHom) := by
    rw [show evalC t0 = (augPair (Euc (2 * j)) y0).comp Φ.toAlgHom
      from AlgHom.ext fun h => (hΦ y0 hy0 h).symm]
    exact sphKT_K0.mapA_comp Φ.toAlgHom (augPair (Euc (2 * j)) y0)
  obtain ⟨⟨g', hg'mem, hg'inf, hg'gen⟩, hpsi2, hpsi3⟩ :=
    (sphKT_ball_K (Euc (2 * j)) y0 hy0 j).1 (finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 2 * j))
  have key : ∀ z : K0 C(Sph V, ℂ),
      K0.mapA (augPair (Euc (2 * j)) y0) (K0.mapA Φ.toAlgHom z) = K0.mapA (evalC t0) z := by
    intro z
    rw [hχ]
    rfl
  refine ⟨⟨K0.mapA (Φ.symm).toAlgHom g', ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [← key, sphKT_K0.mapA_apply_symm]; exact hg'mem
  · intro k hk
    have : k • g' = 0 := by
      have h := congrArg (K0.mapA Φ.toAlgHom) hk
      simpa only [map_zsmul, sphKT_K0.mapA_apply_symm, map_zero] using h
    exact hg'inf k this
  · intro z hz
    obtain ⟨k, hk⟩ := hg'gen (K0.mapA Φ.toAlgHom z) (by rw [key]; exact hz)
    exact ⟨k, by rw [← sphKT_K0.mapA_symm_apply Φ z, hk, map_zsmul]⟩
  · intro ψ hψ z hz
    obtain ⟨ψ', hψ'⟩ := (psi_exists.1 (Kpair (Euc (2 * j))) (fun x y => mul_comm x y)).1
    have hnat := (psi_exists.2.1 (C(Sph V, ℂ)) (Kpair (Euc (2 * j))) (fun x y => mul_comm x y) (fun x y => mul_comm x y) Φ.toAlgHom ψ ψ').1 hψ hψ'
    have hz' : K0.mapA (augPair (Euc (2 * j)) y0) (K0.mapA Φ.toAlgHom z) = 0 := by
      rw [key]; exact hz
    have h1 : K0.mapA Φ.toAlgHom (ψ z) = K0.mapA Φ.toAlgHom ((2 ^ j : ℤ) • z) := by
      rw [hnat z, hpsi2 ψ' hψ' _ hz', map_zsmul]
    exact sphKT_K0.mapA_injective Φ h1
  · intro ψ hψ z hz
    obtain ⟨ψ', hψ'⟩ := (psi_exists.1 (Kpair (Euc (2 * j))) (fun x y => mul_comm x y)).2
    have hnat := (psi_exists.2.1 (C(Sph V, ℂ)) (Kpair (Euc (2 * j))) (fun x y => mul_comm x y) (fun x y => mul_comm x y) Φ.toAlgHom ψ ψ').2 hψ hψ'
    have hz' : K0.mapA (augPair (Euc (2 * j)) y0) (K0.mapA Φ.toAlgHom z) = 0 := by
      rw [key]; exact hz
    have h1 : K0.mapA Φ.toAlgHom (ψ z) = K0.mapA Φ.toAlgHom ((3 ^ j : ℤ) • z) := by
      rw [hnat z, hpsi3 ψ' hψ' _ hz', map_zsmul]
    exact sphKT_K0.mapA_injective Φ h1

lemma sphere_K_even_aux (t0 : Sph V) (j : ℕ)
    (hV : Module.finrank ℝ V = 2 * j + 2) :
    ∀ z : K0 C(Sph V, ℂ), K0.mapA (evalC t0) z = 0 → z = 0 :=
  sphere_K_even V j hV t0

end Main

/-! ## The base case `S^0`: two-point sphere -/

lemma sphKT_antipode_ne_self {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (t0 : Sph V) :
    antipode t0 ≠ t0 := by
  intro h
  have h2 : -(t0 : V) = (t0 : V) := by rw [← antipode_coe, h]
  have h3 : (t0 : V) + (t0 : V) = 0 := by
    nth_rewrite 2 [show (t0 : V) = -(t0 : V) from h2.symm]
    exact add_neg_cancel (t0 : V)
  have h4 : (t0 : V) = 0 := by
    have h5 : (2 : ℝ) • (t0 : V) = 0 := by rw [two_smul]; exact h3
    rcases smul_eq_zero.mp h5 with h6 | h6
    · exact absurd h6 (by norm_num)
    · exact h6
  have h7 := sphKT_norm_coe_sph t0
  rw [h4, norm_zero] at h7
  exact one_ne_zero h7.symm

lemma sphKT_sph_eq_or {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (t0 : Sph V) (hV : Module.finrank ℝ V = 1) (x : Sph V) :
    x = t0 ∨ x = antipode t0 := by
  have hspan : Submodule.span ℝ {(t0 : V)} = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_singleton (sphKT_ne_zero_of_sph t0), hV]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (show (x : V) ∈ Submodule.span ℝ {(t0 : V)} from by rw [hspan]; exact Submodule.mem_top)
  have hc1 : |c| = 1 := by
    have h2 : ‖(x : V)‖ = |c| := by
      rw [← hc, norm_smul, sphKT_norm_coe_sph t0, mul_one, Real.norm_eq_abs]
    rw [sphKT_norm_coe_sph x] at h2
    exact h2.symm
  rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hc1 with h | h
  · left; apply Subtype.ext; rw [← hc, h, one_smul]
  · right; apply Subtype.ext; rw [← hc, h, neg_one_smul]; rfl

lemma sphKT_discreteTopology_sph {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (t0 : Sph V) (hV : Module.finrank ℝ V = 1) :
    DiscreteTopology (Sph V) := by
  have hsurj : Function.Surjective (fun b : Bool => if b then t0 else antipode t0) := by
    intro x
    rcases sphKT_sph_eq_or t0 hV x with h | h
    · exact ⟨true, by simp [h]⟩
    · exact ⟨false, by simp [h]⟩
  haveI : Finite (Sph V) := Finite.of_surjective _ hsurj
  exact Finite.instDiscreteTopology

/-- `C(S^0, ℂ) ≅ ℂ × ℂ` by the two evaluations. -/
lemma sphKT_exists_algEquiv_two {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (t0 : Sph V) (hV : Module.finrank ℝ V = 1) :
    ∃ Φ : C(Sph V, ℂ) ≃ₐ[ℂ] ℂ × ℂ,
      (∀ h, (Φ h).1 = h t0) ∧ (∀ h, (Φ h).2 = h (antipode t0)) := by
  classical
  haveI := sphKT_discreteTopology_sph t0 hV
  have htwo := sphKT_sph_eq_or t0 hV
  let f : C(Sph V, ℂ) →ₐ[ℂ] ℂ × ℂ := (evalC t0).prod (evalC (antipode t0))
  have hf1 : ∀ h, (f h).1 = h t0 := fun h => rfl
  have hf2 : ∀ h, (f h).2 = h (antipode t0) := fun h => rfl
  have hinj : Function.Injective f := by
    intro h h' hh
    ext x
    rcases htwo x with rfl | rfl
    · exact congrArg Prod.fst hh
    · exact congrArg Prod.snd hh
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨⟨fun x => if x = t0 then y.1 else y.2, continuous_of_discreteTopology⟩, ?_⟩
    apply Prod.ext
    · show (if t0 = t0 then y.1 else y.2) = y.1
      rw [if_pos rfl]
    · show (if antipode t0 = t0 then y.1 else y.2) = y.2
      rw [if_neg (sphKT_antipode_ne_self t0)]
  exact ⟨AlgEquiv.ofBijective f ⟨hinj, hsurj⟩, hf1, hf2⟩

/-! ## The cube root of unity and the `1 × 1` computations -/

section Aux

lemma sphKT_omega_cube : omega ^ 3 = 1 := by
  rw [omega, ← Complex.exp_nat_mul]
  have h : ((3 : ℕ) : ℂ) * (2 * ↑Real.pi * Complex.I / 3) = 2 * ↑Real.pi * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_two_pi_mul_I]

lemma sphKT_omega_re : omega.re = -1/2 := by
  have hz : (2 * ↑Real.pi * Complex.I / 3 : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [omega, hz, Complex.exp_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, Real.exp_zero,
    one_mul, Complex.mul_I_im, Complex.ofReal_re]
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub,
    Real.cos_pi_div_three]
  norm_num

lemma sphKT_omega_ne_one : omega ≠ 1 := by
  intro h
  have h1 : omega.re = (1 : ℂ).re := by rw [h]
  rw [sphKT_omega_re, Complex.one_re] at h1
  norm_num at h1

lemma sphKT_omega_inv_eq : omega⁻¹ = omega ^ 2 :=
  inv_eq_of_mul_eq_one_right (by rw [← pow_succ', show 2 + 1 = 3 from rfl, sphKT_omega_cube])

lemma sphKT_omega_inv_sq : omega⁻¹ ^ 2 = omega := by
  rw [sphKT_omega_inv_eq, show (omega^2)^2 = omega^4 by ring, show (4:ℕ) = 3 + 1 by norm_num,
    pow_add, sphKT_omega_cube, one_mul, pow_one]

lemma sphKT_omega_inv_sum : (1:ℂ) + omega⁻¹ + omega⁻¹ ^ 2 = 0 := by
  have h1 : omega ^ 2 + omega + 1 = 0 := by
    have h2 : (omega - 1) * (omega ^ 2 + omega + 1) = 0 := by
      have h3 : (omega - 1) * (omega ^ 2 + omega + 1) = omega ^ 3 - 1 := by ring
      rw [h3, sphKT_omega_cube]; ring
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (sub_ne_zero.mpr sphKT_omega_ne_one)
    · exact h
  rw [sphKT_omega_inv_sq, sphKT_omega_inv_eq, show (1:ℂ) + omega^2 + omega = omega^2 + omega + 1 by ring, h1]

lemma sphKT_swapPerm_one_eq : (swapPerm 1 : Equiv.Perm (Fin (1 * 1))) = Equiv.refl _ := by
  haveI : Subsingleton (Fin (1 * 1)) := inferInstanceAs (Subsingleton (Fin 1))
  refine Equiv.ext (fun x => ?_)
  exact Subsingleton.elim _ _

lemma sphKT_cycPerm_one_eq : (cycPerm 1 : Equiv.Perm (Fin (1 * 1 * 1))) = Equiv.refl _ := by
  haveI : Subsingleton (Fin (1 * 1 * 1)) := inferInstanceAs (Subsingleton (Fin 1))
  refine Equiv.ext (fun x => ?_)
  exact Subsingleton.elim _ _

lemma sphKT_kronMat_eq_mul {A : Type} [Ring A] (M N : Matrix (Fin 1) (Fin 1) A) :
    kronMat M N = M * N := by
  ext i j
  fin_cases i; fin_cases j
  simp only [kronMat, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton]
  congr 1 <;> (congr 1 <;> exact Subsingleton.elim _ _)

lemma sphKT_proj_pos {A : Type} [Ring A] [Algebra ℂ A] :
    (algebraMap ℂ A (1/2 : ℂ)) • ((1 : Matrix (Fin 1) (Fin 1) A)
      + (algebraMap ℂ A (1 : ℂ)) • (1 : Matrix (Fin 1) (Fin 1) A)) = 1 := by
  ext i j; fin_cases i; fin_cases j
  show (algebraMap ℂ A (1/2 : ℂ)) * ((1 : A) + (algebraMap ℂ A (1 : ℂ)) * 1) = 1
  rw [_root_.map_one, mul_one, show (1 : A) + 1 = algebraMap ℂ A 2 by rw [map_ofNat, one_add_one_eq_two],
    ← map_mul, show (1/2 : ℂ) * 2 = 1 by norm_num, _root_.map_one]

lemma sphKT_proj_neg {A : Type} [Ring A] [Algebra ℂ A] :
    (algebraMap ℂ A (1/2 : ℂ)) • ((1 : Matrix (Fin 1) (Fin 1) A)
      + (algebraMap ℂ A (-1 : ℂ)) • (1 : Matrix (Fin 1) (Fin 1) A)) = 0 := by
  ext i j; fin_cases i; fin_cases j
  show (algebraMap ℂ A (1/2 : ℂ)) * ((1 : A) + (algebraMap ℂ A (-1 : ℂ)) * 1) = 0
  rw [map_neg, _root_.map_one, neg_mul, one_mul, add_neg_cancel, mul_zero]

lemma sphKT_proj_three {A : Type} [Ring A] [Algebra ℂ A] :
    (algebraMap ℂ A (1/3 : ℂ)) • ((1 : Matrix (Fin 1) (Fin 1) A)
      + (algebraMap ℂ A ((1:ℂ)⁻¹)) • (1 : Matrix (Fin 1) (Fin 1) A)
      + (algebraMap ℂ A (((1:ℂ)⁻¹)^2)) • ((1 : Matrix (Fin 1) (Fin 1) A)
          * (1 : Matrix (Fin 1) (Fin 1) A))) = 1 := by
  rw [Matrix.mul_one]
  ext i j; fin_cases i; fin_cases j
  show (algebraMap ℂ A (1/3 : ℂ)) * ((1 : A) + (algebraMap ℂ A ((1:ℂ)⁻¹)) * 1
      + (algebraMap ℂ A (((1:ℂ)⁻¹)^2)) * 1) = 1
  simp only [inv_one, one_pow, _root_.map_one, mul_one]
  rw [show (1 : A) + 1 + 1 = algebraMap ℂ A 3 by rw [map_ofNat]; norm_num,
    ← map_mul, show (1/3 : ℂ) * 3 = 1 by norm_num, _root_.map_one]

lemma sphKT_proj_omega {A : Type} [Ring A] [Algebra ℂ A] :
    (algebraMap ℂ A (1/3 : ℂ)) • ((1 : Matrix (Fin 1) (Fin 1) A)
      + (algebraMap ℂ A omega⁻¹) • (1 : Matrix (Fin 1) (Fin 1) A)
      + (algebraMap ℂ A (omega⁻¹ ^ 2)) • ((1 : Matrix (Fin 1) (Fin 1) A)
          * (1 : Matrix (Fin 1) (Fin 1) A))) = 0 := by
  rw [Matrix.mul_one]
  ext i j; fin_cases i; fin_cases j
  show (algebraMap ℂ A (1/3 : ℂ)) * ((1 : A) + (algebraMap ℂ A omega⁻¹) * 1
      + (algebraMap ℂ A (omega⁻¹ ^ 2)) * 1) = 0
  rw [mul_one, mul_one,
    show (1 : A) + algebraMap ℂ A omega⁻¹ + algebraMap ℂ A (omega⁻¹ ^ 2)
        = algebraMap ℂ A ((1:ℂ) + omega⁻¹ + (omega⁻¹)^2) by rw [map_add, map_add, _root_.map_one],
    sphKT_omega_inv_sum, map_zero, mul_zero]

lemma sphKT_sq2Part_one_one_eq {A : Type} [Ring A] [Algebra ℂ A] (M : Matrix (Fin 1) (Fin 1) A) :
    sq2Part (1 : ℂ) (⟨1, M⟩ : Mat A) = ⟨1, M * M⟩ := by
  have hmain : (kronMat M M : Matrix (Fin 1) (Fin 1) A) *
      ((algebraMap ℂ A (1/2 : ℂ)) • ((1 : Matrix (Fin 1) (Fin 1) A)
        + (algebraMap ℂ A (1 : ℂ)) • (1 : Matrix (Fin 1) (Fin 1) A))) = M * M := by
    rw [sphKT_kronMat_eq_mul, sphKT_proj_pos]; exact mul_one _
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    simp only [sq2Part]
    rw [show swapPerm 1 = (Equiv.refl _ : Equiv.Perm (Fin (1*1))) from sphKT_swapPerm_one_eq,
      Matrix.permMatrix_refl]
    exact hmain

lemma sphKT_sq2Part_neg_one_one_zero {A : Type} [Ring A] [Algebra ℂ A] (M : Matrix (Fin 1) (Fin 1) A) :
    (sq2Part (-1 : ℂ) (⟨1, M⟩ : Mat A)).2 = 0 := by
  have hmain : (kronMat M M : Matrix (Fin 1) (Fin 1) A) *
      ((algebraMap ℂ A (1/2 : ℂ)) • ((1 : Matrix (Fin 1) (Fin 1) A)
        + (algebraMap ℂ A (-1 : ℂ)) • (1 : Matrix (Fin 1) (Fin 1) A))) = 0 := by
    rw [sphKT_kronMat_eq_mul, sphKT_proj_neg]; exact mul_zero _
  simp only [sq2Part]
  rw [show swapPerm 1 = (Equiv.refl _ : Equiv.Perm (Fin (1*1))) from sphKT_swapPerm_one_eq,
    Matrix.permMatrix_refl]
  exact hmain

lemma sphKT_cubePart_one_one_eq {A : Type} [Ring A] [Algebra ℂ A] (M : Matrix (Fin 1) (Fin 1) A) :
    cubePart (1 : ℂ) (⟨1, M⟩ : Mat A) = ⟨1, M * M * M⟩ := by
  have hmain : (kronMat (kronMat M M) M : Matrix (Fin 1) (Fin 1) A) *
      ((algebraMap ℂ A (1/3 : ℂ)) • ((1 : Matrix (Fin 1) (Fin 1) A)
        + (algebraMap ℂ A ((1:ℂ)⁻¹)) • (1 : Matrix (Fin 1) (Fin 1) A)
        + (algebraMap ℂ A (((1:ℂ)⁻¹)^2)) • ((1 : Matrix (Fin 1) (Fin 1) A)
            * (1 : Matrix (Fin 1) (Fin 1) A)))) = M * M * M := by
    rw [sphKT_kronMat_eq_mul, sphKT_kronMat_eq_mul, sphKT_proj_three]; exact mul_one _
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    simp only [cubePart]
    rw [show cycPerm 1 = (Equiv.refl _ : Equiv.Perm (Fin (1*1*1))) from sphKT_cycPerm_one_eq,
      Matrix.permMatrix_refl]
    exact hmain

lemma sphKT_cubePart_omega_one_zero {A : Type} [Ring A] [Algebra ℂ A] (M : Matrix (Fin 1) (Fin 1) A) :
    (cubePart omega (⟨1, M⟩ : Mat A)).2 = 0 := by
  have hmain : (kronMat (kronMat M M) M : Matrix (Fin 1) (Fin 1) A) *
      ((algebraMap ℂ A (1/3 : ℂ)) • ((1 : Matrix (Fin 1) (Fin 1) A)
        + (algebraMap ℂ A omega⁻¹) • (1 : Matrix (Fin 1) (Fin 1) A)
        + (algebraMap ℂ A (omega⁻¹ ^ 2)) • ((1 : Matrix (Fin 1) (Fin 1) A)
            * (1 : Matrix (Fin 1) (Fin 1) A)))) = 0 := by
    rw [sphKT_kronMat_eq_mul, sphKT_kronMat_eq_mul, sphKT_proj_omega]; exact mul_zero _
  simp only [cubePart]
  rw [show cycPerm 1 = (Equiv.refl _ : Equiv.Perm (Fin (1*1*1))) from sphKT_cycPerm_one_eq,
    Matrix.permMatrix_refl]
  exact hmain

lemma sphKT_psi2Cls_one_one {A : Type} [Ring A] [Algebra ℂ A] (M : Matrix (Fin 1) (Fin 1) A)
    (hM : M * M = M) :
    psi2Cls (⟨1, M⟩ : Mat A) = cls (⟨1, M⟩ : Mat A) := by
  have hp : Mat.IsIdem (⟨1, M⟩ : Mat A) := hM
  rw [psi2Cls, if_pos hp, sphKT_sq2Part_one_one_eq M, hM,
    show cls (sq2Part (-1 : ℂ) (⟨1, M⟩ : Mat A)) = 0 from
      sphKT_cls_of_zero (sphKT_sq2Part_neg_one_one_zero M)]
  rw [sub_zero]

lemma sphKT_psi3Cls_one_one {A : Type} [Ring A] [Algebra ℂ A] (M : Matrix (Fin 1) (Fin 1) A)
    (hM : M * M = M) :
    psi3Cls (⟨1, M⟩ : Mat A) = cls (⟨1, M⟩ : Mat A) := by
  have hp : Mat.IsIdem (⟨1, M⟩ : Mat A) := hM
  rw [psi3Cls, if_pos hp, sphKT_cls_of_zero (sphKT_cubePart_omega_one_zero M),
    sphKT_cubePart_one_one_eq M, show M * M * M = M by rw [mul_assoc, hM, hM]]
  rw [sub_zero]


end Aux

section ZeroMain

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma sphere_K_zero_aux (t0 : Sph V) (hV : Module.finrank ℝ V = 1) :
    (∃ g : K0 C(Sph V, ℂ), K0.mapA (evalC t0) g = 0 ∧ (∀ k : ℤ, k • g = 0 → k = 0) ∧
        ∀ z, K0.mapA (evalC t0) z = 0 → ∃ k : ℤ, z = k • g) ∧
    (∀ ψ : K0 C(Sph V, ℂ) →+ K0 C(Sph V, ℂ), IsPsi2 ψ →
        ∀ z, K0.mapA (evalC t0) z = 0 → ψ z = z) ∧
    (∀ ψ : K0 C(Sph V, ℂ) →+ K0 C(Sph V, ℂ), IsPsi3 ψ →
        ∀ z, K0.mapA (evalC t0) z = 0 → ψ z = z) := by
  obtain ⟨Φ₀, hΦ₁, hΦ₂⟩ := sphKT_exists_algEquiv_two t0 hV
  obtain ⟨e₀, he₀⟩ := K0_prod ℂ ℂ
  obtain ⟨ez, hez⟩ := k0_basic.2.2.2.2
  have hfst : (RingHom.fst ℂ ℂ).comp Φ₀.toAlgHom.toRingHom = (evalC t0).toRingHom := by
    ext h; exact hΦ₁ h
  have hsnd : (RingHom.snd ℂ ℂ).comp Φ₀.toAlgHom.toRingHom = (evalC (antipode t0)).toRingHom := by
    ext h; exact hΦ₂ h
  have hE1 : ∀ z, (e₀ (K0.map Φ₀.toAlgHom.toRingHom z)).1 = K0.mapA (evalC t0) z := by
    intro z
    rw [he₀]
    change K0.map (RingHom.fst ℂ ℂ) (K0.map Φ₀.toAlgHom.toRingHom z) = _
    rw [show K0.map (RingHom.fst ℂ ℂ) (K0.map Φ₀.toAlgHom.toRingHom z)
        = ((K0.map (RingHom.fst ℂ ℂ)).comp (K0.map Φ₀.toAlgHom.toRingHom)) z from rfl,
      ← k0_basic.2.2.1 (A := C(Sph V, ℂ)) (B := ℂ × ℂ) (C := ℂ)
        Φ₀.toAlgHom.toRingHom (RingHom.fst ℂ ℂ), hfst]
  have hE2 : ∀ z, (e₀ (K0.map Φ₀.toAlgHom.toRingHom z)).2 = K0.mapA (evalC (antipode t0)) z := by
    intro z
    rw [he₀]
    change K0.map (RingHom.snd ℂ ℂ) (K0.map Φ₀.toAlgHom.toRingHom z) = _
    rw [show K0.map (RingHom.snd ℂ ℂ) (K0.map Φ₀.toAlgHom.toRingHom z)
        = ((K0.map (RingHom.snd ℂ ℂ)).comp (K0.map Φ₀.toAlgHom.toRingHom)) z from rfl,
      ← k0_basic.2.2.1 (A := C(Sph V, ℂ)) (B := ℂ × ℂ) (C := ℂ)
        Φ₀.toAlgHom.toRingHom (RingHom.snd ℂ ℂ), hsnd]
  let P : Mat (ℂ × ℂ) := ⟨1, Matrix.of (fun _ _ : Fin 1 => ((1 : ℂ), (0 : ℂ)))⟩
  let one : Mat (ℂ × ℂ) := ⟨1, (1 : Matrix (Fin 1) (Fin 1) (ℂ × ℂ))⟩
  have hPidem : Mat.IsIdem P := by
    show P.2 * P.2 = P.2
    apply Matrix.ext
    intro i j; fin_cases i; fin_cases j
    simp only [P, Matrix.of_apply, Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton,
      Prod.mk_mul_mk, mul_one, mul_zero]
  have honeidem : Mat.IsIdem one := by
    change (1 : Matrix (Fin 1) (Fin 1) (ℂ × ℂ)) * 1 = 1
    rw [mul_one]
  have hmapfstP : Mat.map (RingHom.fst ℂ ℂ) P = Mat.one ℂ 1 := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Matrix.ext
      intro i j; fin_cases i; fin_cases j
      simp [P, Mat.map, Mat.one]
  have hmapfstone : Mat.map (RingHom.fst ℂ ℂ) one = Mat.one ℂ 1 := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Matrix.ext
      intro i j; fin_cases i; fin_cases j
      simp [one, Mat.map, Mat.one]
  have hmapsndone : Mat.map (RingHom.snd ℂ ℂ) one = Mat.one ℂ 1 := by
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Matrix.ext
      intro i j; fin_cases i; fin_cases j
      simp [one, Mat.map, Mat.one]
  have hmapsndPzero : (Mat.map (RingHom.snd ℂ ℂ) P).2 = 0 := by
    apply Matrix.ext
    intro i j; fin_cases i; fin_cases j
    simp [P, Mat.map]
  have hfstP : K0.map (RingHom.fst ℂ ℂ) (cls P) = cls (Mat.one ℂ 1) := by
    rw [sphKT_K0.map_cls (RingHom.fst ℂ ℂ) hPidem, hmapfstP]
  have hfstone : K0.map (RingHom.fst ℂ ℂ) (cls one) = cls (Mat.one ℂ 1) := by
    rw [sphKT_K0.map_cls (RingHom.fst ℂ ℂ) honeidem, hmapfstone]
  have hsndone : K0.map (RingHom.snd ℂ ℂ) (cls one) = cls (Mat.one ℂ 1) := by
    rw [sphKT_K0.map_cls (RingHom.snd ℂ ℂ) honeidem, hmapsndone]
  have hsndP : K0.map (RingHom.snd ℂ ℂ) (cls P) = 0 := by
    rw [sphKT_K0.map_cls (RingHom.snd ℂ ℂ) hPidem,
      show cls (Mat.map (RingHom.snd ℂ ℂ) P) = 0 from sphKT_cls_of_zero hmapsndPzero]
  have hz₀ : cls (Mat.one ℂ 1) = ez.symm 1 := by rw [← hez, AddEquiv.symm_apply_apply]
  let g : K0 C(Sph V, ℂ) := K0.mapA Φ₀.symm.toAlgHom (cls P - cls one)
  have hg' : K0.mapA Φ₀.toAlgHom g = cls P - cls one := sphKT_K0.mapA_apply_symm Φ₀ _
  have hge : e₀ (cls P - cls one) = (0, ez.symm (-1)) := by
    rw [he₀, Prod.mk.injEq]
    constructor
    · rw [map_sub, hfstP, hfstone, sub_self]
    · rw [map_sub, hsndP, hsndone, hz₀, zero_sub,
        show -(ez.symm 1) = ez.symm (-1) from by rw [← map_neg]]
  have hker : K0.mapA (evalC t0) g = 0 := by
    change K0.map (evalC t0).toRingHom g = 0
    rw [← hfst]
    change K0.map ((RingHom.fst ℂ ℂ).comp Φ₀.toAlgHom.toRingHom) g = 0
    rw [k0_basic.2.2.1 (A := C(Sph V, ℂ)) (B := ℂ × ℂ) (C := ℂ)
        Φ₀.toAlgHom.toRingHom (RingHom.fst ℂ ℂ)]
    change K0.map (RingHom.fst ℂ ℂ) (K0.map Φ₀.toAlgHom.toRingHom g) = 0
    rw [show K0.map Φ₀.toAlgHom.toRingHom g = cls P - cls one from hg',
      map_sub, hfstP, hfstone, sub_self]
  have hgenz : ∀ z, K0.mapA (evalC t0) z = 0 → ∃ k : ℤ, z = k • g := by
    intro z hz
    set w : K0 (ℂ × ℂ) := K0.map Φ₀.toAlgHom.toRingHom z with hw
    have hz1 : K0.map (RingHom.fst ℂ ℂ) (K0.map Φ₀.toAlgHom.toRingHom z) = 0 := by
      simpa [he₀, hz] using hE1 z
    have hw1 : (e₀ w).1 = 0 := by rw [he₀]; exact hz1
    have keyb : ∀ c : K0 ℂ, (-(ez c)) • ez.symm (-1) = c := by
      intro c
      rw [show ez.symm (-1) = -(ez.symm 1) from by rw [← map_neg], smul_neg, neg_zsmul,
        neg_neg, ← map_zsmul, show (ez c) • (1 : ℤ) = ez c by simp, AddEquiv.symm_apply_apply]
    set b : K0 ℂ := (e₀ w).2 with hb
    set n' : ℤ := -(ez b) with hn'
    have hw2 : e₀ w = (0, b) := by rw [hb, ← hw1]
    have hbval : n' • ez.symm (-1) = b := by rw [hn']; exact keyb b
    have hwval : w = n' • (cls P - cls one) := by
      calc w = e₀.symm (e₀ w) := (AddEquiv.symm_apply_apply e₀ w).symm
        _ = e₀.symm (0, b) := by rw [hw2]
        _ = e₀.symm (0, n' • ez.symm (-1)) := by rw [← hbval]
        _ = e₀.symm (n' • (0, ez.symm (-1))) := by rw [Prod.smul_mk, smul_zero]
        _ = n' • e₀.symm (0, ez.symm (-1)) := by rw [map_zsmul]
        _ = n' • (cls P - cls one) := by
              rw [show e₀.symm (0, ez.symm (-1)) = cls P - cls one from by
                rw [← hge, AddEquiv.symm_apply_apply]]
    refine ⟨n', ?_⟩
    rw [show z = K0.mapA Φ₀.symm.toAlgHom (K0.mapA Φ₀.toAlgHom z) from
      (sphKT_K0.mapA_symm_apply Φ₀ z).symm]
    rw [show K0.mapA Φ₀.toAlgHom z = w from hw.symm, hwval, map_zsmul]
  have hψ2 : ∀ ψ : K0 C(Sph V, ℂ) →+ K0 C(Sph V, ℂ), IsPsi2 ψ → ψ g = g := by
    intro ψ hψ
    obtain ⟨ψ', hψ'⟩ := (psi_exists.1 (ℂ × ℂ) (fun x y => mul_comm x y)).1
    have hnat := (psi_exists.2.1 (C(Sph V, ℂ)) (ℂ × ℂ) (fun x y => mul_comm x y) (fun x y => mul_comm x y) Φ₀.toAlgHom ψ ψ').1 hψ hψ'
    have hP' : ψ' (cls P - cls one) = cls P - cls one := by
      have h1 : ψ' (cls P) = cls P := by rw [hψ' P]; exact sphKT_psi2Cls_one_one P.2 hPidem
      have h2 : ψ' (cls one) = cls one := by rw [hψ' one]; exact sphKT_psi2Cls_one_one one.2 honeidem
      rw [map_sub, h1, h2]
    exact sphKT_K0.mapA_injective Φ₀ (by rw [hnat g, hg', hP', ← hg'])
  have hψ3 : ∀ ψ : K0 C(Sph V, ℂ) →+ K0 C(Sph V, ℂ), IsPsi3 ψ → ψ g = g := by
    intro ψ hψ
    obtain ⟨ψ', hψ'⟩ := (psi_exists.1 (ℂ × ℂ) (fun x y => mul_comm x y)).2
    have hnat := (psi_exists.2.1 (C(Sph V, ℂ)) (ℂ × ℂ) (fun x y => mul_comm x y) (fun x y => mul_comm x y) Φ₀.toAlgHom ψ ψ').2 hψ hψ'
    have hP' : ψ' (cls P - cls one) = cls P - cls one := by
      have h1 : ψ' (cls P) = cls P := by rw [hψ' P]; exact sphKT_psi3Cls_one_one P.2 hPidem
      have h2 : ψ' (cls one) = cls one := by rw [hψ' one]; exact sphKT_psi3Cls_one_one one.2 honeidem
      rw [map_sub, h1, h2]
    exact sphKT_K0.mapA_injective Φ₀ (by rw [hnat g, hg', hP', ← hg'])
  refine ⟨⟨g, hker, ?_, hgenz⟩, ?_, ?_⟩
  · intro k hk
    have h1 : k • (cls P - cls one) = 0 := by
      have h := congrArg (K0.mapA Φ₀.toAlgHom) hk
      rw [map_zsmul, map_zero] at h
      rw [show K0.mapA Φ₀.toAlgHom g = cls P - cls one from hg'] at h
      exact h
    have h2 : k • (-(ez.symm 1)) = 0 := by
      have h := congrArg (K0.map (RingHom.snd ℂ ℂ)) h1
      simpa only [map_zsmul, map_sub, hsndP, hsndone, zero_sub, map_zero, hz₀] using h
    have h3 : k = 0 := by
      have h := congrArg ez h2
      rw [map_zsmul, map_zero, map_neg, AddEquiv.apply_symm_apply] at h
      simp at h
      omega
    exact h3
  · intro ψ hψ z hz
    obtain ⟨k, rfl⟩ := hgenz z hz
    rw [map_zsmul, hψ2 ψ hψ]
  · intro ψ hψ z hz
    obtain ⟨k, rfl⟩ := hgenz z hz
    rw [map_zsmul, hψ3 ψ hψ]

end ZeroMain


/-! ## The target theorem -/

theorem sphere_K (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (t0 : Sph V) (j : ℕ) :
    (Module.finrank ℝ V = 2 * j + 1 →
      (∃ g : K0 C(Sph V, ℂ), K0.mapA (evalC t0) g = 0 ∧ (∀ k : ℤ, k • g = 0 → k = 0) ∧
        ∀ z, K0.mapA (evalC t0) z = 0 → ∃ k : ℤ, z = k • g) ∧
      (∀ ψ : K0 C(Sph V, ℂ) →+ K0 C(Sph V, ℂ), IsPsi2 ψ →
        ∀ z, K0.mapA (evalC t0) z = 0 → ψ z = (2 ^ j : ℤ) • z) ∧
      (∀ ψ : K0 C(Sph V, ℂ) →+ K0 C(Sph V, ℂ), IsPsi3 ψ →
        ∀ z, K0.mapA (evalC t0) z = 0 → ψ z = (3 ^ j : ℤ) • z)) ∧
    (Module.finrank ℝ V = 2 * j + 2 → ∀ z, K0.mapA (evalC t0) z = 0 → z = 0) := by
  constructor
  · intro hV
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have h := sphere_K_zero_aux V t0 (by omega)
      exact ⟨h.1, fun ψ hψ z hz => by simpa using h.2.1 ψ hψ z hz,
        fun ψ hψ z hz => by simpa using h.2.2 ψ hψ z hz⟩
    · exact sphere_K_odd_aux V t0 j hj hV
  · intro hV
    exact sphere_K_even_aux V t0 j hV

end

end Work.KT
