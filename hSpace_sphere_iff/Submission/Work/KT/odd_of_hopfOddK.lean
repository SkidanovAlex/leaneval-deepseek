import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.k0_basic
import Submission.Work.KT.psi_exists
import Submission.Work.KT.psi_comm
import Submission.Work.KT.cone_exact
import Submission.Work.KT.sphere_K
import Submission.Work.KT.ball_K
import Submission.Work.KT.sphere_GL
import Submission.Work.KT.aa_algebra
import Submission.Work.Hopf.dvd_two_pow_three_pow_sub_one
import Submission.Work.Hopf.two_pow_dvd_of_psi_relation

/-! Adams–Atiyah: a map `S^{4m-1} → S^{2m}` of odd `K`-theoretic Hopf invariant exists only for
`m = 1, 2, 4`. -/

namespace Work.KT

/-! ## Functoriality helpers for `K₀` and for `ℤ`-scalars -/

lemma oddK_mapA_comp {A B C : Type} [Ring A] [Ring B] [Ring C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C] (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) :
    K0.mapA (ψ.comp φ) = (K0.mapA ψ).comp (K0.mapA φ) :=
  k0_basic.2.2.1 A B C φ.toRingHom ψ.toRingHom

lemma oddK_mapA_id {A : Type} [Ring A] [Algebra ℂ A] :
    K0.mapA (AlgHom.id ℂ A) = AddMonoidHom.id (K0 A) :=
  k0_basic.2.2.2.1 A

lemma oddK_mapA_mapA {A B C : Type} [Ring A] [Ring B] [Ring C]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C] (φ : A →ₐ[ℂ] B) (ψ : B →ₐ[ℂ] C) (x : K0 A) :
    K0.mapA ψ (K0.mapA φ x) = K0.mapA (ψ.comp φ) x :=
  (DFunLike.congr_fun (oddK_mapA_comp φ ψ) x).symm

lemma oddK_nsmul_eq_int_nsmul {G : Type} [AddCommGroup G] (n : ℕ) (x : G) :
    n • x = (n : ℤ) • x := by
  induction n with
  | zero => simp
  | succ k ih => rw [succ_nsmul, ih]; push_cast; rw [add_zsmul, one_zsmul]

lemma oddK_mapA_evalC_ofId {T : Type} [TopologicalSpace T] (t0 : T) (x : K0 ℂ) :
    K0.mapA (evalC t0) (K0.mapA (Algebra.ofId ℂ C(T, ℂ)) x) = x := by
  rw [oddK_mapA_mapA (Algebra.ofId ℂ C(T, ℂ)) (evalC t0) x,
      show (evalC t0).comp (Algebra.ofId ℂ C(T, ℂ)) = AlgHom.id ℂ ℂ from rfl, oddK_mapA_id]
  rfl

/-- `K₀ C(T, ℂ)` is torsion-free when `K₀ ℂ ≅ ℤ` splits off and the reduced part is infinite
cyclic.  This is the `2`-torsion-freeness input consumed by `aa_algebra`. -/
lemma oddK_torsion_free_of_cyclic_kernel {T : Type} [TopologicalSpace T] (t0 : T)
    (g : K0 C(T, ℂ))
    (hgen : ∀ z, K0.mapA (evalC t0) z = 0 → ∃ k : ℤ, z = k • g)
    (hnz : ∀ k : ℤ, k • g = 0 → k = 0) :
    ∀ z : K0 C(T, ℂ), 2 • z = 0 → z = 0 := by
  obtain ⟨e, _he⟩ := k0_basic.2.2.2.2
  intro z hz
  set w : K0 ℂ := K0.mapA (evalC t0) z with hwdef
  have hw2 : (2 : ℕ) • w = 0 := by rw [hwdef, ← map_nsmul, hz, map_zero]
  have hw0 : w = 0 := by
    have h2 : (2 : ℕ) • (e w) = 0 := by rw [← map_nsmul, hw2, map_zero]
    rw [nsmul_eq_mul] at h2
    have h3 : e w = 0 := by omega
    exact e.injective (by rw [h3, map_zero])
  set z1 : K0 C(T, ℂ) := K0.mapA (Algebra.ofId ℂ C(T, ℂ)) w with hz1def
  have hz1eval : K0.mapA (evalC t0) z1 = w := oddK_mapA_evalC_ofId t0 w
  have hz1zero : z1 = 0 := by rw [hz1def, hw0, map_zero]
  set z2 : K0 C(T, ℂ) := z - z1 with hz2def
  have hz2z : z2 = z := by rw [hz2def, hz1zero, sub_zero]
  have hz2eval : K0.mapA (evalC t0) z2 = 0 := by
    rw [hz2def, map_sub, hz1eval, ← hwdef, sub_self]
  obtain ⟨k, hk⟩ := hgen z2 hz2eval
  have hz2zero : z2 = 0 := by
    have h2z2 : (2 : ℕ) • z2 = 0 := by rw [hz2z, hz]
    have h2k : ((2 : ℤ) * k) • g = 0 := by
      rw [hk] at h2z2
      rw [oddK_nsmul_eq_int_nsmul, smul_smul] at h2z2
      exact h2z2
    have hk0 : k = 0 := by
      have := hnz ((2 : ℤ) * k) h2k
      omega
    rw [hk, hk0, zero_zsmul]
  rw [← hz2z]
  exact hz2zero

set_option maxHeartbeats 4000000

/-- Adams–Atiyah: a map `S^{4m-1} → S^{2m}` of odd `K`-theoretic Hopf invariant exists only for
`m = 1, 2, 4`. -/
theorem odd_of_hopfOddK (m : ℕ) (hm : 1 ≤ m) (f : C(Sph (Eu m × Eu m), Tgt m))
    (hf : HopfOddK m f) : m = 1 ∨ m = 2 ∨ m = 4 := by
  obtain ⟨t0, y0, hy0, a, β, h, hh, ha, hβ, hβgen, hμaa⟩ := hf
  haveI : Nonempty (Tgt m) :=
    ⟨⟨EuclideanSpace.single (0 : Fin (2 * m + 1)) (1 : ℝ), by simp [PiLp.norm_single]⟩⟩
  have hcommC : ∀ x y : coneAlg f, x * y = y * x :=
    fun x y => Subtype.ext (mul_comm x.val y.val)
  have hcommT : ∀ x y : C(Tgt m, ℂ), x * y = y * x := fun x y => mul_comm x y
  have hcommV : ∀ x y : Kpair (Eu m × Eu m), x * y = y * x :=
    fun x y => Subtype.ext (mul_comm x.val y.val)
  obtain ⟨ψc2, hψc2⟩ := (psi_exists.1 (coneAlg f) hcommC).1
  obtain ⟨ψc3, hψc3⟩ := (psi_exists.1 (coneAlg f) hcommC).2
  obtain ⟨ψT2, hψT2⟩ := (psi_exists.1 C(Tgt m, ℂ) hcommT).1
  obtain ⟨ψT3, hψT3⟩ := (psi_exists.1 C(Tgt m, ℂ) hcommT).2
  obtain ⟨ψV2, hψV2⟩ := (psi_exists.1 (Kpair (Eu m × Eu m)) hcommV).1
  obtain ⟨ψV3, hψV3⟩ := (psi_exists.1 (Kpair (Eu m × Eu m)) hcommV).2
  obtain ⟨μ, hμ, _hμcomm, _hμassoc, _hμone⟩ := (k0_basic.1 (coneAlg f) hcommC)
  set b : K0 (coneAlg f) := K0.mapA (relToCone f y0 hy0) β with hbdef
  have hTfin : Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * m + 1))) = 2 * m + 1 := by simp
  have hVfin : Module.finrank ℝ (Eu m × Eu m) = 2 * (2 * m) := by
    simp [Eu, Module.finrank_prod]; ring
  obtain ⟨hsp1, hsp2⟩ := (sphere_K (EuclideanSpace ℝ (Fin (2 * m + 1))) t0 m).1 hTfin
  obtain ⟨gT, _hgTred, hgTnz, hgTgen⟩ := hsp1
  have hTψ2 : ∀ z, K0.mapA (evalC t0) z = 0 → ψT2 z = (2 ^ m : ℤ) • z := hsp2.1 ψT2 hψT2
  have hTψ3 : ∀ z, K0.mapA (evalC t0) z = 0 → ψT3 z = (3 ^ m : ℤ) • z := hsp2.2 ψT3 hψT3
  obtain ⟨hba1, hba2⟩ := (ball_K (Eu m × Eu m) y0 hy0 (2 * m)).1 hVfin
  obtain ⟨gV, hgVred, hgVnz, hgVgen⟩ := hba1
  have hVψ2 : ∀ z, K0.mapA (augPair (Eu m × Eu m) y0) z = 0 →
      ψV2 z = (2 ^ (2 * m) : ℤ) • z := hba2.1 ψV2 hψV2
  have hVψ3 : ∀ z, K0.mapA (augPair (Eu m × Eu m) y0) z = 0 →
      ψV3 z = (3 ^ (2 * m) : ℤ) • z := hba2.2 ψV3 hψV3
  have hGLT : GLStablyTrivial (Tgt m) :=
    sphere_GL (EuclideanSpace ℝ (Fin (2 * m + 1))) m hTfin
  have hcex := cone_exact (Eu m × Eu m) (Tgt m) f y0 hy0
  -- `β` has infinite order
  have hβnz : ∀ k : ℤ, k • β = 0 → k = 0 := by
    intro k hk
    obtain ⟨k2, hk2⟩ := hgVgen β hβ
    have hgV0 : gV ≠ 0 := by
      intro h0
      have h1 : (1 : ℤ) • gV = 0 := by rw [h0, smul_zero]
      exact one_ne_zero (hgVnz 1 h1)
    have hk2nz : k2 ≠ 0 := by
      intro h0
      rw [h0, zero_zsmul] at hk2
      obtain ⟨k1, hk1⟩ := hβgen gV hgVred
      rw [hk2, smul_zero] at hk1
      exact hgV0 hk1
    have h2 : (k * k2) • gV = 0 := by
      rw [← smul_smul, ← hk2, hk]
    exact (mul_eq_zero.mp (hgVnz (k * k2) h2)).resolve_right hk2nz
  -- the generator `b` of `K̃(C_f)` has infinite order, by injectivity of `relToCone`
  have hb : ∀ k : ℤ, k • b = 0 → k = 0 := by
    intro k hk
    have hk'' : K0.mapA (relToCone f y0 hy0) (k • β) = 0 := by
      rw [map_zsmul, ← hbdef, hk]
    have hred : K0.mapA (augPair (Eu m × Eu m) y0) (k • β) = 0 := by
      rw [map_zsmul, hβ, smul_zero]
    exact hβnz k (hcex.2.2 hGLT (k • β) hred hk'')
  -- the reduced part of `K(C_f)` is generated by `b`
  have hker : ∀ x : K0 (coneAlg f), K0.mapA (coneToT f) x = 0 → ∃ k : ℤ, x = k • b := by
    intro x hx
    obtain ⟨w, hw1, hw2⟩ := hcex.1 x hx
    obtain ⟨k, hk⟩ := hβgen w hw1
    exact ⟨k, by rw [← hw2, hk, map_zsmul, ← hbdef]⟩
  have hcomp : (coneToT f).comp (relToCone f y0 hy0)
      = (Algebra.ofId ℂ C(Tgt m, ℂ)).comp (augPair (Eu m × Eu m) y0) := by
    ext hh0; rfl
  have hib : K0.mapA (coneToT f) b = 0 := by
    rw [hbdef, oddK_mapA_mapA (relToCone f y0 hy0) (coneToT f) β, hcomp,
        ← oddK_mapA_mapA (augPair (Eu m × Eu m) y0) (Algebra.ofId ℂ C(Tgt m, ℂ)) β,
        hβ, map_zero]
  have hψV2β : ψV2 β = (2 ^ (2 * m) : ℤ) • β := hVψ2 β hβ
  have hψV3β : ψV3 β = (3 ^ (2 * m) : ℤ) • β := hVψ3 β hβ
  have hψb2 : ψc2 b = (2 ^ (2 * m) : ℤ) • b := by
    rw [hbdef, ← (psi_exists.2.1 (Kpair (Eu m × Eu m)) (coneAlg f) hcommV hcommC
        (relToCone f y0 hy0) ψV2 ψc2).1 hψV2 hψc2 β, hψV2β, map_zsmul]
  have hψb3 : ψc3 b = (3 ^ (2 * m) : ℤ) • b := by
    rw [hbdef, ← (psi_exists.2.1 (Kpair (Eu m × Eu m)) (coneAlg f) hcommV hcommC
        (relToCone f y0 hy0) ψV3 ψc3).2 hψV3 hψc3 β, hψV3β, map_zsmul]
  have ha' : K0.mapA (evalC t0) (K0.mapA (coneToT f) a) = 0 := by
    rw [oddK_mapA_mapA (coneToT f) (evalC t0) a]
    exact ha
  have hψa2 : K0.mapA (coneToT f) (ψc2 a) = (2 ^ m : ℤ) • K0.mapA (coneToT f) a := by
    rw [(psi_exists.2.1 (coneAlg f) C(Tgt m, ℂ) hcommC hcommT (coneToT f) ψc2 ψT2).1
        hψc2 hψT2 a, hTψ2 (K0.mapA (coneToT f) a) ha']
  have hψa3 : K0.mapA (coneToT f) (ψc3 a) = (3 ^ m : ℤ) • K0.mapA (coneToT f) a := by
    rw [(psi_exists.2.1 (coneAlg f) C(Tgt m, ℂ) hcommC hcommT (coneToT f) ψc3 ψT3).2
        hψc3 hψT3 a, hTψ3 (K0.mapA (coneToT f) a) ha']
  have hsq : ∃ y, ψc2 a - h • b = 2 • y := by
    obtain ⟨y, hy⟩ := (psi_exists.2.2.2 (coneAlg f) hcommC μ ψc2 hμ hψc2) a
    exact ⟨y, by rw [← hy, hμaa μ hμ, hbdef]⟩
  have hcomm := psi_comm (coneAlg f) hcommC ψc2 ψc3 hψc2 hψc3
  have hA : ∀ z : K0 C(Tgt m, ℂ), 2 • z = 0 → z = 0 :=
    oddK_torsion_free_of_cyclic_kernel t0 gT hgTgen hgTnz
  have hdiv : (2 : ℤ) ^ m ∣ (3 : ℤ) ^ m - 1 :=
    aa_algebra (K0 (coneAlg f)) (K0 C(Tgt m, ℂ)) (K0.mapA (coneToT f)) ψc2 ψc3 a b m hm
      h hh hcomm hA hker hib hb hψb2 hψb3 hψa2 hψa3 hsq
  apply Work.Hopf.dvd_two_pow_three_pow_sub_one m hm
  have h3 : (((3 : ℕ) ^ m - 1 : ℕ) : ℤ) = (3 : ℤ) ^ m - 1 := by
    have h1 : (1 : ℕ) ≤ 3 ^ m := Nat.one_le_pow m 3 (by norm_num)
    rw [Nat.cast_sub h1, Nat.cast_pow]; norm_num
  rw [← h3] at hdiv
  exact_mod_cast hdiv

end Work.KT
