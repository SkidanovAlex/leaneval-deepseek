import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.TotallySplit
import Submission.Work.Models.Port.Commons.LinearAlgebra.FiniteDimensional.finrank_ker_eq_one_of_comp_self_eq_zero
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.center_SL2_eq_bot_of_charTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped LinearAlgebra.Projectivization Matrix MatrixGroups

namespace Commons.GroupTheory.SL2

/-- The action of a matrix `g ∈ SL(2,K)` on the projective line is given on the level of
vectors by multiplication by `g`. -/
private lemma smul_mk_toLin {K : Type*} [Field K] (g : Matrix.SpecialLinearGroup (Fin 2) K)
    (v : Fin 2 → K) (hv : v ≠ 0) :
    g • (Projectivization.mk K v hv : Projectivization K (Fin 2 → K))
      = Projectivization.mk K (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K) v)
        (by rw [Matrix.toLin'_apply]; exact (smul_ne_zero_iff_ne g).mpr hv) := by
  rw [Projectivization.smul_mk]; congr 1

/-- In characteristic two, an involution of `SL(2,K)` (different from the identity) fixes a
unique point of the projective line: the one spanned by a nonzero vector in the kernel of
`g - 1`, where `g - 1` is a nonzero nilpotent endomorphism. -/
theorem existsUnique_fixedPoint_specialLinearGroup_involution {K : Type*} [Field K]
    (hchar : CharP K 2) (g : Matrix.SpecialLinearGroup (Fin 2) K) (hg2 : g ^ 2 = 1)
    (hg1 : g ≠ 1) :
    ∃! x : Projectivization K (Fin 2 → K), g • x = x := by
  classical
  have hMM : (g : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) K =>
      (x : Matrix (Fin 2) (Fin 2) K)) hg2
    rwa [pow_two, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at h
  have hMne : (g : Matrix (Fin 2) (Fin 2) K) ≠ 1 := by
    intro h
    exact hg1 (Subtype.ext (by simpa using h))
  set f : (Fin 2 → K) →ₗ[K] (Fin 2 → K) :=
    Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K) with hf
  have hf2 : f.comp f = LinearMap.id := by
    rw [hf, ← Matrix.toLin'_mul, hMM, Matrix.toLin'_one]
  have hfne : f ≠ LinearMap.id := by
    intro h
    apply hMne
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_one]
    exact hf ▸ h
  set T : (Fin 2 → K) →ₗ[K] (Fin 2 → K) := f - LinearMap.id with hT
  have hTne : T ≠ 0 := by
    intro h
    apply hfne
    have h' : f - LinearMap.id = 0 := by rw [← hT]; exact h
    exact sub_eq_zero.mp h'
  have hneg1 : (-1 : K) = 1 := by
    rw [neg_one_eq_one_iff]
    exact (ringChar.eq_iff (R := K) (p := 2)).mpr hchar
  have hneg : ∀ w : Fin 2 → K, -w = w := by
    intro w
    rw [← neg_one_smul K w, hneg1, one_smul]
  have hfv : ∀ v : Fin 2 → K, f (f v) = v := by
    intro v
    have h := congrArg (fun u : (Fin 2 → K) →ₗ[K] (Fin 2 → K) => u v) hf2
    simpa using h
  have hT2 : T.comp T = 0 := by
    apply LinearMap.ext
    intro v
    rw [hT]
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, LinearMap.sub_apply, LinearMap.id_apply,
      map_sub, hfv v]
    have h1 : v - f v = f v - v := by
      rw [sub_eq_add_neg, sub_eq_add_neg, hneg (f v), hneg v, add_comm]
    rw [h1, sub_self]
  have hfin : Module.finrank K (Fin 2 → K) = 2 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hrank : Module.finrank K T.ker = 1 :=
    Commons.LinearAlgebra.FiniteDimensional.finrank_ker_eq_one_of_comp_self_eq_zero
      hfin T hT2 hTne
  haveI : Module.Free K ↥T.ker := Module.Free.of_divisionRing K _
  obtain ⟨w0, hw0, hspan⟩ := (finrank_eq_one_iff' (K := K) (V := ↥T.ker)).mp hrank
  set w : Fin 2 → K := (w0 : Fin 2 → K) with hwdef
  have hw : w ≠ 0 := by
    intro h
    exact hw0 (Subtype.ext (by simpa [hwdef] using h))
  have hwfix : f w = w := by
    have hmem : T w = 0 := by
      have := LinearMap.mem_ker.mp w0.2
      simpa [hwdef] using this
    have h1 : f w - w = 0 := by simpa [hT, LinearMap.sub_apply] using hmem
    exact sub_eq_zero.mp h1
  refine ⟨Projectivization.mk K w hw, ?_, ?_⟩
  · change g • Projectivization.mk K w hw = Projectivization.mk K w hw
    have hgw : g • w = w := by
      change Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K) w = w
      exact hwfix
    rw [Projectivization.smul_mk]
    simp only [hgw]
  · intro y hy
    induction y using Projectivization.ind with
    | h v hv =>
      have hv' : Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K) v ≠ 0 := by
        rw [Matrix.toLin'_apply]; exact (smul_ne_zero_iff_ne g).mpr hv
      have hy' : Projectivization.mk K (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K) v) hv'
          = Projectivization.mk K v hv := by
        rw [← smul_mk_toLin g v hv, hy]
      obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' K
        (Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K) v) v hv' hv).mp hy'
      have ha2 : a * a = 1 := by
        have hv'2 : (a * a) • v = (1 : K) • v := by
          calc (a * a) • v = a • (a • v) := by rw [mul_smul]
            _ = a • f v := by rw [ha, hf]
            _ = f (a • v) := by rw [LinearMap.map_smul]
            _ = f (f v) := by rw [ha, hf]
            _ = v := hfv v
            _ = (1 : K) • v := by rw [one_smul]
        have hz : (a * a - 1) • v = 0 := by rw [sub_smul, hv'2, sub_self]
        rcases (smul_eq_zero.mp hz) with h | h
        · exact sub_eq_zero.mp h
        · exact absurd h hv
      have ha1 : a = 1 := by
        have h : a ^ 2 = 1 := by rw [pow_two]; exact ha2
        rcases (sq_eq_one_iff.mp h) with h | h
        · exact h
        · rw [h, hneg1]
      have hfv_eq : f v = v := by
        change Matrix.toLin' (g : Matrix (Fin 2) (Fin 2) K) v = v
        rw [← ha, ha1, one_smul]
      have hvker : v ∈ T.ker := by
        rw [LinearMap.mem_ker, hT, LinearMap.sub_apply, LinearMap.id_apply, hfv_eq, sub_self]
      obtain ⟨c, hc⟩ := hspan ⟨v, hvker⟩
      have hcw : c • w = v := by
        have := congrArg (Subtype.val) hc
        simpa [hwdef, Submodule.coe_smul] using this
      have hc0 : c ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hcw
        exact hv hcw.symm
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨c, hcw⟩

/-- In a finite field `K` of characteristic two, every involution `t` of the projective special
linear group `PSL(2,K)` fixes a unique point of the projective line `ℙ¹(K)`. -/
theorem existsUnique_fixedPoint_involution_projectiveSpecialLinearGroup {K : Type*} [Field K]
    [Fintype K] (hchar : CharP K 2) (a : Projectivization K (Fin 2 → K)) :
    ∀ t : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K, orderOf t = 2 →
      ∃! x : Projectivization K (Fin 2 → K), t • x = x := by
  intro t ht
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) t
  have hg' : (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) = t := hg
  have ht' : t ^ 2 = 1 ∧ t ≠ 1 := (orderOf_eq_prime_iff (p := 2)).mp ht
  have hmem : g ^ 2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [← QuotientGroup.eq_one_iff]
    show (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))) (g ^ 2) = 1
    rw [map_pow, hg, ht'.1]
  have hg2 : g ^ 2 = 1 := by
    have h := hmem
    rw [Commons.LinearAlgebra.Matrix.center_SL2_eq_bot_of_charTwo (F := K)] at h
    simpa using h
  have hg1 : g ≠ 1 := by
    intro h
    exact ht'.2 (by rw [← hg', h]; simp)
  obtain ⟨x, hx, huniq⟩ := existsUnique_fixedPoint_specialLinearGroup_involution hchar g hg2 hg1
  refine ⟨x, ?_, ?_⟩
  · change t • x = x
    rw [← hg']
    rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk]
    exact hx
  · intro y hy
    refine huniq y ?_
    rw [← hg'] at hy
    rwa [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk] at hy

end Commons.GroupTheory.SL2