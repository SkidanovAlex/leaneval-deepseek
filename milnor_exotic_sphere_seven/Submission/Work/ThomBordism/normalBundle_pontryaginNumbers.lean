import Mathlib
import Submission.Work.Tubular.exists_euclidean_normalBundle
import Submission.Work.Thom.manifoldP1
import Submission.Work.ThomBordism.normalWhitneyTorsion
import Submission.Work.ThomBordism.PontryaginThom.Normal

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Pontryagin numbers of the normal bundle, from the Whitney relation

`Work.ThomBordism.normalWhitneyTorsion` records the Whitney relation `p(TV) ⌣ p(ν) = 1` for the
normal bundle `ν` of an embedding `V ⊂ ℝ^{8+k}` only up to torsion: a positive multiple of
`p₁(ν) + p₁(TV)` (resp. of `p₂(ν) + p₁(ν) ⌣ p₁(TV) + p₂(TV)`) vanishes in cohomology.  This is
enough to identify the *numbers*: the Pontryagin numbers of `ν` are the tangent ones,

`p̄₁² = p₁²`,   `p̄₂ = p₁² - p₂`,

because an integral pairing of a torsion class with the fundamental class vanishes.  Together with
`Work.ThomBordism.PontryaginThom.NormalBundlData.normalP1Sq_eq` and `…normalP2_eq` this gives the
two number identities of `NormalBundlData` for the *actual* normal bundle.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

attribute [local implicit_reducible]
  Work.Cohomology.singularCohomology
  Work.Cohomology.singularCochainComplex
  Work.Cohomology.SSetCochainComplex
  AlgebraicTopology.singularChainComplexFunctor

namespace Work.ThomBordism

open Work.Cohomology Work.Thom Work.SignatureBordism Work.ThomBordism.PontryaginThom

noncomputable section

/-! ## The linear-algebra core -/

/-- **Torsion in degree `4` kills the intersection numbers.**  If a nonzero multiple of `a + b`
vanishes, then for every bilinear form `F` the self-intersections of `a` and `b` agree and the cross
term is the negative self-intersection of `b`. -/
theorem torsion_pair_core {M : Type*} [AddCommGroup M] [Module ℤ M] {m : ℤ} (hm : m ≠ 0)
    (F : M →ₗ[ℤ] M →ₗ[ℤ] ℤ) (a b : M) (h : m • (a + b) = 0) :
    F a a = F b b ∧ F a b = - F b b := by
  have key : ∀ y : M, m * F (a + b) y = 0 := by
    intro y
    have hc := congrArg (fun w => F w y) h
    rw [map_zsmul] at hc
    rw [LinearMap.smul_apply, LinearMap.map_zero, LinearMap.zero_apply, smul_eq_mul] at hc
    exact hc
  have hpa : F (a + b) a = 0 := (mul_eq_zero.mp (key a)).resolve_left hm
  have hpb : F (a + b) b = 0 := (mul_eq_zero.mp (key b)).resolve_left hm
  have hbp : F b (a + b) = 0 := by
    have hc := congrArg (fun w => F b w) h
    rw [map_zsmul] at hc
    rw [LinearMap.map_zero, smul_eq_mul] at hc
    exact (mul_eq_zero.mp hc).resolve_left hm
  rw [LinearMap.map_add, LinearMap.add_apply] at hpa hpb
  rw [LinearMap.map_add] at hbp
  constructor <;> linarith

/-- **Torsion in degree `8` kills the pairings.**  If a nonzero multiple of `x + y + z` vanishes,
then `G x + G y + G z = 0` for every linear functional `G`. -/
theorem torsion_sum_core {M : Type*} [AddCommGroup M] [Module ℤ M] {m : ℤ} (hm : m ≠ 0)
    (G : M →ₗ[ℤ] ℤ) (x y z : M) (h : m • (x + y + z) = 0) :
    G x + G y + G z = 0 := by
  have key : m * G (x + y + z) = 0 := by
    have hc := congrArg G h
    rw [map_zsmul] at hc
    rw [LinearMap.map_zero, smul_eq_mul] at hc
    exact hc
  have h0 : G (x + y + z) = 0 := (mul_eq_zero.mp key).resolve_left hm
  have h1 : G x + G y + G z = 0 := by
    simpa only [LinearMap.map_add, LinearMap.add_apply] using h0
  exact h1

/-! ## The two number identities -/

theorem normalBundle_pontryaginNumbers {V : Work.ThomBordism.Man8} {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
    (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
    [Fintype (Work.ThomBordism.PontryaginThom.CoverIdx V k)]
    (N : Work.ThomBordism.PontryaginThom.NormalBundlData V) :
    (Work.Cohomology.kronH ℤ (Work.ThomBordism.PontryaginThom.ssetOf V.pt) 8
        (Work.Cohomology.cupH' ℤ (Work.ThomBordism.PontryaginThom.ssetOf V.pt) 4 4
          (Work.Thom.pontryagin1 (Work.Tubular.normalBundle E ND))
          (Work.Thom.pontryagin1 (Work.Tubular.normalBundle E ND))) V.c = N.normalP1Sq) ∧
    (Work.Cohomology.kronH ℤ (Work.ThomBordism.PontryaginThom.ssetOf V.pt) 8
        (show (Work.Cohomology.cochainC ℤ (Work.ThomBordism.PontryaginThom.ssetOf V.pt)).homology 8 from
          (by norm_num : 4 * 2 = 8) ▸ Work.Thom.pontryaginClass 2 (Work.Tubular.normalBundle E ND))
        V.c = N.normalP2) := by
  obtain ⟨N₁, hN₁, h₁⟩ := (normalWhitneyTorsion E ND).1
  obtain ⟨N₂, hN₂, h₂⟩ := (normalWhitneyTorsion E ND).2
  have hN₁' : (N₁ : ℤ) ≠ 0 := by exact_mod_cast hN₁.ne'
  have hN₂' : (N₂ : ℤ) ≠ 0 := by exact_mod_cast hN₂.ne'
  let a : ↑(Work.Thom.Coh ℤ 4 V.pt) :=
    (pontryagin1 (Work.Tubular.normalBundle E ND) : ↑(Work.Thom.Coh ℤ 4 V.pt))
  let b : ↑(Work.Thom.Coh ℤ 4 V.pt) := show ↑(Work.Thom.Coh ℤ 4 V.pt) from V.p1
  have hA : (N₁ : ℤ) • (show ↑(Work.Thom.Coh ℤ 4 V.pt) from (a + b)) = 0 := h₁
  have h4 := torsion_pair_core hN₁'
    (F := interForm ℤ (ssetOf V.pt) 4 4 V.c) (a := a) (b := b) (h := hA)
  let q : ↑(Work.Thom.Coh ℤ 8 V.pt) :=
    show ↑(Work.Thom.Coh ℤ 8 V.pt) from
      ((by norm_num : 4 * 2 = 8) ▸ pontryaginClass 2 (Work.Tubular.normalBundle E ND))
  let cc : ↑(Work.Thom.Coh ℤ 8 V.pt) :=
    show ↑(Work.Thom.Coh ℤ 8 V.pt) from
      ((by norm_num : 4 + 4 = 8) ▸ cupH' ℤ (ssetOf V.pt) 4 4 a b)
  let p2c : ↑(Work.Thom.Coh ℤ 8 V.pt) := show ↑(Work.Thom.Coh ℤ 8 V.pt) from V.p2
  have hB : (N₂ : ℤ) • (show ↑(Work.Thom.Coh ℤ 8 V.pt) from (q + cc + p2c)) = 0 := h₂
  let G : ↑(Work.Thom.Coh ℤ 8 V.pt) →ₗ[ℤ] ℤ :=
    (LinearMap.applyₗ V.c).comp (kronH ℤ (ssetOf V.pt) 8)
  have h8 := torsion_sum_core hN₂' (G := G) (x := q) (y := cc) (z := p2c) (h := hB)
  have h8a : G q = kronH ℤ (ssetOf V.pt) 8 q V.c := rfl
  have h8b : G cc = interForm ℤ (ssetOf V.pt) 4 4 V.c a b := rfl
  have h8c : G p2c = kronH ℤ (ssetOf V.pt) 8 p2c V.c := rfl
  have hp2 : kronH ℤ (ssetOf V.pt) 8 p2c V.c = V.p2Num := rfl
  have hbb : interForm ℤ (ssetOf V.pt) 4 4 V.c b b = V.p1Sq := rfl
  have hfin : kronH ℤ (ssetOf V.pt) 8 q V.c
      + interForm ℤ (ssetOf V.pt) 4 4 V.c a b + V.p2Num = 0 := by
    rw [h8a, h8b, h8c, hp2] at h8
    exact h8
  refine ⟨?_, ?_⟩
  · rw [N.normalP1Sq_eq]
    exact h4.1
  · rw [N.normalP2_eq]
    rw [h4.2, hbb] at hfin
    show kronH ℤ (ssetOf V.pt) 8 q V.c = V.p1Sq - V.p2Num
    linarith

end

end Work.ThomBordism
