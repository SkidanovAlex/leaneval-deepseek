import Mathlib
import Submission.Work.ZassenhausSuzuki.SingerModelDefs
import Submission.Work.Models.PSL2.pslEquiv
import Submission.Work.Hering.AppVIII.QuadExtNorm
import Submission.Work.ZassenhausSuzuki.SingerModelCycle.Defs
import Submission.Work.ZassenhausSuzuki.SingerModelCycle.exists_anisotropic
import Submission.Work.ZassenhausSuzuki.SingerModelCycle.card_sup_zpowers_of_inverts
import Submission.Work.ZassenhausSuzuki.SingerModelCycle.transport_singer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Singer cycle in `PSL(2, 2ⁿ)`

For `n ≥ 2` the group `PSL(2, 2ⁿ) = SL(2, 2ⁿ)` (the centre of `SL(2,F)` is trivial in
characteristic two) contains a cyclic subgroup `V` — the *Singer cycle* / non-split torus — of
order `2ⁿ + 1` with

* `C(V) = V`,
* `|N(V)| = 2 (2ⁿ + 1)`,
* an involution `τ` with `τ v τ = v⁻¹` for all `v ∈ V` (so in particular every element of `V`
  is a product of two involutions).

The subgroup is realised concretely as the image in `SL(2,F)` of the norm-one subgroup of the
quadratic extension `L = F[α]`, `α² = εα + 1`, under the regular representation
(`singerSubgroup ε` of `Submission.Work.ZassenhausSuzuki.SingerModelDefs`), and the result is
transported to `PSL2Model n = PSL(2, 2ⁿ)` along `Work.Models.PSL2.pslEquiv`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

namespace Work.ZassenhausSuzuki.SingerModelCycle

open Work.Hering.AppVIII
open Work.ZassenhausSuzuki

variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-! ## The Singer cycle is cyclic of order `|F| + 1` -/

/-- The regular representation of the norm-one subgroup is injective. -/
theorem injective_normOneToSL (ε : F) : Function.Injective (normOneToSL ε) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  apply quadAlgHom_injective ε
  exact congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F)) hxy

/-- The norm-one subgroup has order `|F| + 1`: it is the kernel of the `(|F|+1)`-st power map
on the cyclic group `Lˣ` of order `|F|² - 1`. -/
theorem card_normOne {ε : F} (h : Anisotropic F ε) :
    Nat.card ↥(normOne ε) = Nat.card F + 1 := by
  haveI : Fact (Irreducible (quadPoly F ε)) := ⟨quadPoly_irreducible F h⟩
  have hker : normOne ε = (powMonoidHom (Nat.card F + 1)).ker := by
    ext y
    rw [mem_normOne_iff_pow h y, MonoidHom.mem_ker, powMonoidHom_apply]
  rw [hker, IsCyclic.card_powMonoidHom_ker]
  have hcard : Nat.card (QuadExt F ε)ˣ = Nat.card F ^ 2 - 1 := by
    rw [Nat.card_units, quadExt_natCard F ε]
  rw [hcard]
  have hsq : Nat.card F ^ 2 - 1 = (Nat.card F - 1) * (Nat.card F + 1) := by
    have h1 := Nat.sq_sub_sq (Nat.card F) 1
    rw [h1, mul_comm]
  rw [hsq, Nat.gcd_comm]
  exact Nat.gcd_eq_left (dvd_mul_left _ _)

/-- The Singer cycle has order `|F| + 1`. -/
theorem card_singerSubgroup {ε : F} (h : Anisotropic F ε) :
    Nat.card ↥(singerSubgroup ε) = Nat.card F + 1 := by
  have hcard : Nat.card ↥(singerSubgroup ε) = Nat.card ↥(normOne ε) :=
    (Nat.card_congr (MonoidHom.ofInjective (injective_normOneToSL ε)).toEquiv).symm
  rw [hcard, card_normOne h]

/-- The Singer cycle is cyclic. -/
theorem isCyclic_singerSubgroup {ε : F} (h : Anisotropic F ε) :
    IsCyclic ↥(singerSubgroup ε) := by
  haveI : Fact (Irreducible (quadPoly F ε)) := ⟨quadPoly_irreducible F h⟩
  haveI : IsCyclic ↥(normOne ε) := inferInstance
  exact isCyclic_of_surjective
    (MonoidHom.ofInjective (injective_normOneToSL ε)).toMonoidHom
    (MonoidHom.ofInjective (injective_normOneToSL ε)).surjective

/-! ## The Singer cycle is self-centralising, with normaliser of order `2(|F|+1)` -/

/-- **The Frobenius involution inverts the Singer cycle**: `τ v τ = v⁻¹` for `v` in the Singer
cycle, where `τ = !![1, ε; 0, 1]` is the matrix of the Frobenius `x ↦ x ^ |F|` of `L`. -/
theorem frobSL_mul_mem_mul_frobSL {ε : F} (h : Anisotropic F ε)
    {v : Matrix.SpecialLinearGroup (Fin 2) F} (hv : v ∈ singerSubgroup ε) :
    frobSL ε * v * frobSL ε = v⁻¹ := by
  have key : ∀ x : ↥(normOne ε),
      (frobSL ε * (normOneToSL ε x) * frobSL ε) * (normOneToSL ε x) = 1 := by
    intro x
    have hy : (((x : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε) ^ Nat.card F
        * (((x : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε) = 1 :=
      normOne_pow_mul h x.2
    have hconj := frobSL_conj_quadAlgHom h (((x : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε)
    have hcoe : ((normOneToSL ε x : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F)
        = quadAlgHom ε (((x : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε) := rfl
    apply Subtype.ext
    change (frobSL ε : Matrix (Fin 2) (Fin 2) F)
        * ((normOneToSL ε x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        * (frobSL ε : Matrix (Fin 2) (Fin 2) F)
        * ((normOneToSL ε x : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1
    rw [hcoe, hconj, ← map_mul, hy, map_one]
  obtain ⟨x, rfl⟩ := hv
  exact eq_inv_of_mul_eq_one_left (key x)

/-- **The Singer cycle is self-centralising in `SL(2,F)`.**  Every element commuting with the
whole cycle commutes in particular with `α`; the matrices commuting with the matrix of `α` are
exactly the elements of the image of `L`, and among those the determinant-one ones are the
norm-one elements. -/
theorem centralizer_singerSubgroup {ε : F} (h : Anisotropic F ε) :
    Subgroup.centralizer (singerSubgroup ε : Set (Matrix.SpecialLinearGroup (Fin 2) F))
      = singerSubgroup ε := by
  refine le_antisymm ?_ ?_
  · intro g hg
    have hcomm : alphaSL ε * g = g * alphaSL ε :=
      (Subgroup.mem_centralizer_iff.mp hg) (alphaSL ε) (alphaSL_mem_singerSubgroup ε)
    have hm : (g : Matrix (Fin 2) (Fin 2) F) * (qalphaMat ε)
        = (qalphaMat ε) * (g : Matrix (Fin 2) (Fin 2) F) := by
      have h2 : ((alphaSL ε : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F))
          = ((g : Matrix (Fin 2) (Fin 2) F) * (alphaSL ε : Matrix (Fin 2) (Fin 2) F)) :=
        congrArg (fun u : Matrix.SpecialLinearGroup (Fin 2) F =>
          (u : Matrix (Fin 2) (Fin 2) F)) hcomm
      rw [alphaSL_coe] at h2
      exact h2.symm
    obtain ⟨a, b, hab⟩ := exists_eq_smul_one_add_of_mul_qalphaMat_comm hm
    exact mem_singerSubgroup_of_coe_eq h hab
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    haveI : IsCyclic ↥(singerSubgroup ε) := isCyclic_singerSubgroup h
    haveI : IsMulCommutative ↥(singerSubgroup ε) := IsCyclic.isMulCommutative
    have hcomm : (⟨w, hw⟩ : ↥(singerSubgroup ε)) * ⟨v, hv⟩
        = ⟨v, hv⟩ * ⟨w, hw⟩ := IsMulCommutative.is_comm.comm _ _
    simpa using congrArg (fun u : ↥(singerSubgroup ε) =>
      (u : Matrix.SpecialLinearGroup (Fin 2) F)) hcomm

/-- **The normaliser of the Singer cycle in `SL(2,F)` is `V ⊔ ⟨τ⟩`** where `τ` is the
Frobenius involution.  The inclusion `⊆` compares the traces and determinants of `A = qalphaMat`
and `g A g⁻¹ ∈ V`; the two possibilities `g A g⁻¹ = A` and `g A g⁻¹ = A + ε` give `g ∈ V` and
`g ∈ V τ` respectively. -/
theorem normalizer_singerSubgroup {ε : F} (h : Anisotropic F ε) :
    Subgroup.normalizer (singerSubgroup ε : Set (Matrix.SpecialLinearGroup (Fin 2) F))
      = singerSubgroup ε ⊔ Subgroup.zpowers (frobSL ε) := by
  refine le_antisymm ?_ ?_
  · intro g hg
    have hmem : ∀ v : Matrix.SpecialLinearGroup (Fin 2) F,
        v ∈ singerSubgroup ε → g * v * g⁻¹ ∈ singerSubgroup ε :=
      fun v hv => (Subgroup.mem_normalizer_iff.mp hg v).mp hv
    obtain ⟨a, b, hab⟩ :=
      exists_eq_smul_one_add_of_mem_singerSubgroup (hmem _ (alphaSL_mem_singerSubgroup ε))
    have hX : (g : Matrix (Fin 2) (Fin 2) F) * (qalphaMat ε)
        * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • qalphaMat ε := by
      have h1 : ((g * alphaSL ε * g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F)
          = (g : Matrix (Fin 2) (Fin 2) F) * (alphaSL ε : Matrix (Fin 2) (Fin 2) F)
            * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := rfl
      rw [alphaSL_coe] at h1
      rw [← h1]
      exact hab
    have hQP : ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
        * (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
      have h1 : ((g⁻¹ * g : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F)
          = ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
            * (g : Matrix (Fin 2) (Fin 2) F) := rfl
      rw [inv_mul_cancel] at h1
      exact h1.symm
    have htrace : b * ε = ε := by
      have h1 : Matrix.trace ((g : Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
            * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
          = Matrix.trace (qalphaMat ε) := by
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
      rw [hX, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
        qalphaMat_trace] at h1
      simp only [smul_eq_mul, Fintype.card_fin, Nat.cast_ofNat, CharTwo.two_eq_zero,
        mul_zero, zero_add] at h1
      exact h1
    have hb1 : b = 1 := by
      have hε : ε ≠ 0 := eps_ne_zero F h
      exact mul_right_cancel₀ hε (by rw [htrace, one_mul])
    have hdet : a * a + ε * (a * b) + b * b = 1 := by
      have h1 : ((g : Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
            * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)).det
          = (qalphaMat ε).det := by
        rw [Matrix.det_mul, Matrix.det_mul, Matrix.SpecialLinearGroup.det_coe,
          Matrix.SpecialLinearGroup.det_coe, qalphaMat_det]
        ring
      rw [hX, det_smul_one_add_qalphaMat, qalphaMat_det] at h1
      exact h1
    have ha : a = 0 ∨ a = ε := by
      have h0 : a * (a + ε) = 0 := by
        have h2 : a * a + ε * a = 0 := by
          have h3 : a * a + ε * a + 1 = 1 := by
            have h4 := hdet
            rw [hb1] at h4
            simpa using h4
          calc a * a + ε * a = a * a + ε * a + 1 + 1 := by
                rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
            _ = 0 := by rw [h3, CharTwo.add_self_eq_zero]
        rw [mul_add, mul_comm a ε]
        exact h2
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by
          have h4 : a = -ε := eq_neg_of_add_eq_zero_left h'
          rwa [CharTwo.neg_eq] at h4)
    rcases ha with ha0 | haε
    · have hcommA : (g : Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
          = qalphaMat ε * (g : Matrix (Fin 2) (Fin 2) F) := by
        have h1 : (g : Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
            * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
            = qalphaMat ε := by
          rw [hX, ha0, hb1]
          simp
        calc (g : Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
            = (g : Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
              * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
              * (g : Matrix (Fin 2) (Fin 2) F) := by
              rw [mul_assoc, hQP, mul_one]
            _ = qalphaMat ε * (g : Matrix (Fin 2) (Fin 2) F) := by rw [h1]
      obtain ⟨c, d, hcd⟩ := exists_eq_smul_one_add_of_mul_qalphaMat_comm hcommA
      exact Subgroup.mem_sup_left (mem_singerSubgroup_of_coe_eq h hcd)
    · have h1 : (frobSL ε : Matrix (Fin 2) (Fin 2) F)
          * (qalphaMat ε + ε • (1 : Matrix (Fin 2) (Fin 2) F))
          * (frobSL ε : Matrix (Fin 2) (Fin 2) F) = qalphaMat ε := by
        rw [← frobSL_mul_qalphaMat_mul_frobSL]
        rw [show (frobSL ε : Matrix (Fin 2) (Fin 2) F)
            * ((frobSL ε : Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
              * (frobSL ε : Matrix (Fin 2) (Fin 2) F))
            * (frobSL ε : Matrix (Fin 2) (Fin 2) F)
            = ((frobSL ε : Matrix (Fin 2) (Fin 2) F) * (frobSL ε : Matrix (Fin 2) (Fin 2) F))
              * qalphaMat ε
              * ((frobSL ε : Matrix (Fin 2) (Fin 2) F)
                * (frobSL ε : Matrix (Fin 2) (Fin 2) F)) by noncomm_ring,
          frobSL_mat_mul_self, one_mul, mul_one]
      have h3 : (g : Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
          * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
          = qalphaMat ε + ε • (1 : Matrix (Fin 2) (Fin 2) F) := by
        rw [hX, haε, hb1, one_smul, add_comm]
      have h2 : (frobSL ε : Matrix (Fin 2) (Fin 2) F)
          * ((g : Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
            * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
          * (frobSL ε : Matrix (Fin 2) (Fin 2) F) = qalphaMat ε := by
        rw [h3]
        exact h1
      have hXY : ((frobSL ε * g : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F)
          * ((g⁻¹ * frobSL ε : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) = 1 := by
        have h4 : frobSL ε * g * (g⁻¹ * frobSL ε) = 1 := by
          rw [show frobSL ε * g * (g⁻¹ * frobSL ε) = frobSL ε * frobSL ε by group,
            frobSL_mul_self]
        have h5 := congrArg (fun u : Matrix.SpecialLinearGroup (Fin 2) F =>
          (u : Matrix (Fin 2) (Fin 2) F)) h4
        simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
          using h5
      have hYX : ((g⁻¹ * frobSL ε : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F)
          * ((frobSL ε * g : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) = 1 := by
        have h4 : g⁻¹ * frobSL ε * (frobSL ε * g) = 1 := by
          rw [show g⁻¹ * frobSL ε * (frobSL ε * g)
              = g⁻¹ * (frobSL ε * frobSL ε) * g by group,
            frobSL_mul_self, mul_one, inv_mul_cancel]
        have h5 := congrArg (fun u : Matrix.SpecialLinearGroup (Fin 2) F =>
          (u : Matrix (Fin 2) (Fin 2) F)) h4
        simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
          using h5
      have hX2' : ((frobSL ε * g : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
          * ((g⁻¹ * frobSL ε : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) = qalphaMat ε := by
        rw [show ((frobSL ε * g : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F)
            = (frobSL ε : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F)
            from rfl,
          show ((g⁻¹ * frobSL ε : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F)
            = ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
              * (frobSL ε : Matrix (Fin 2) (Fin 2) F) from rfl]
        rw [show ((frobSL ε : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F))
              * qalphaMat ε
              * (((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
                * (frobSL ε : Matrix (Fin 2) (Fin 2) F))
            = (frobSL ε : Matrix (Fin 2) (Fin 2) F)
              * ((g : Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
                * ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
              * (frobSL ε : Matrix (Fin 2) (Fin 2) F) from by noncomm_ring]
        exact h2
      have hcommX : ((frobSL ε * g : Matrix.SpecialLinearGroup (Fin 2) F) :
          Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
          = qalphaMat ε * ((frobSL ε * g : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F) := by
        calc ((frobSL ε * g : Matrix.SpecialLinearGroup (Fin 2) F) :
              Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
            = ((frobSL ε * g : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
              * (((g⁻¹ * frobSL ε : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F)
                * ((frobSL ε * g : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F)) := by rw [hYX, mul_one]
          _ = (((frobSL ε * g : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
                * ((g⁻¹ * frobSL ε : Matrix.SpecialLinearGroup (Fin 2) F) :
                  Matrix (Fin 2) (Fin 2) F))
              * ((frobSL ε * g : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) := by noncomm_ring
          _ = qalphaMat ε * ((frobSL ε * g : Matrix.SpecialLinearGroup (Fin 2) F) :
                Matrix (Fin 2) (Fin 2) F) := by rw [hX2']
      obtain ⟨c, d, hcd⟩ := exists_eq_smul_one_add_of_mul_qalphaMat_comm hcommX
      have hτgV : frobSL ε * g ∈ singerSubgroup ε := mem_singerSubgroup_of_coe_eq h hcd
      rw [show (singerSubgroup ε ⊔ Subgroup.zpowers (frobSL ε))
          = (Subgroup.zpowers (frobSL ε) ⊔ singerSubgroup ε) from sup_comm _ _]
      rw [show g = frobSL ε * (frobSL ε * g) by
        rw [← mul_assoc, frobSL_mul_self, one_mul]]
      exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers _) hτgV
  · apply sup_le
    · exact Subgroup.le_normalizer
    · apply Subgroup.zpowers_le.mpr
      rw [Subgroup.mem_normalizer_iff]
      intro h'
      constructor
      · intro hh
        rw [frobSL_inv]
        rw [frobSL_mul_mem_mul_frobSL h hh]
        exact Subgroup.inv_mem _ hh
      · intro hh
        rw [frobSL_inv] at hh
        have hx := frobSL_mul_mem_mul_frobSL h hh
        have h2 : frobSL ε * (frobSL ε * h' * frobSL ε) * frobSL ε = h' := by
          rw [show frobSL ε * (frobSL ε * h' * frobSL ε) * frobSL ε
              = (frobSL ε * frobSL ε) * h' * (frobSL ε * frobSL ε) by group,
            frobSL_mul_self, one_mul, mul_one]
        rw [hx] at h2
        rw [← h2]
        exact Subgroup.inv_mem _ hh

/-- The Frobenius involution `τ = frobSL ε` does not lie in the Singer cycle: every element of
the cycle is `a • 1 + b • qalphaMat ε`, symmetric with equal off-diagonal entries `b`, whereas
`τ` has off-diagonal entries `ε ≠ 0` and `0`. -/
theorem frobSL_notMem_singerSubgroup {ε : F} (h : Anisotropic F ε) :
    frobSL ε ∉ singerSubgroup ε := by
  intro hmem
  obtain ⟨a, b, hab⟩ := exists_eq_smul_one_add_of_mem_singerSubgroup hmem
  have h01 : (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • qalphaMat ε) 0 1 = b := by
    simp [qalphaMat, Matrix.add_apply, Matrix.smul_apply]
  have h10 : (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • qalphaMat ε) 1 0 = b := by
    simp [qalphaMat, Matrix.add_apply, Matrix.smul_apply]
  rw [frobSL_coe] at hab
  have e1 : b = ε := by
    have hh := congrFun (congrFun hab 0) 1
    rw [h01] at hh
    simpa using hh.symm
  have e2 : b = 0 := by
    have hh := congrFun (congrFun hab 1) 0
    rw [h10] at hh
    simpa using hh.symm
  exact eps_ne_zero F h (e1 ▸ e2)

/-! ## The model theorem -/

theorem singer_cycle_model {n : ℕ} (hn : 2 ≤ n) :
    ∃ V : Subgroup (LeanEval.GroupTheory.Defs.PSL2Model n), IsCyclic ↥V ∧
      Nat.card ↥V = 2 ^ n + 1 ∧
      Subgroup.centralizer (V : Set (LeanEval.GroupTheory.Defs.PSL2Model n)) = V ∧
      Nat.card ↥(Subgroup.normalizer (V : Set (LeanEval.GroupTheory.Defs.PSL2Model n))) =
        2 * (2 ^ n + 1) ∧
      (∃ τ : LeanEval.GroupTheory.Defs.PSL2Model n, τ * τ = 1 ∧
        ∀ v ∈ V, τ * v * τ = v⁻¹) ∧
      (∀ s ∈ V, ∃ a b : LeanEval.GroupTheory.Defs.PSL2Model n,
        a * a = 1 ∧ b * b = 1 ∧ a * b = s) := by
  obtain ⟨e⟩ := Work.Models.PSL2.pslEquiv n
  obtain ⟨ε, hε⟩ := exists_anisotropic (GaloisField 2 n)
  have hcardF : Nat.card (GaloisField 2 n) = 2 ^ n := by
    have h2 := GaloisField.card 2 n (by omega)
    simpa using h2
  have hcard : Nat.card ↥(singerSubgroup ε) = 2 ^ n + 1 := by
    rw [card_singerSubgroup hε, hcardF]
  have hconj : ∀ v ∈ singerSubgroup ε, frobSL ε * v * (frobSL ε)⁻¹ ∈ singerSubgroup ε := by
    intro v hv
    rw [frobSL_inv, frobSL_mul_mem_mul_frobSL hε hv]
    exact Subgroup.inv_mem _ hv
  have hnorm : Nat.card ↥(Subgroup.normalizer (singerSubgroup ε :
      Set (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)))) = 2 * (2 ^ n + 1) := by
    rw [normalizer_singerSubgroup hε,
      card_sup_zpowers_of_inverts (singerSubgroup ε) (frobSL ε) (frobSL_mul_self ε)
        (frobSL_notMem_singerSubgroup hε) hconj, hcard]
  obtain ⟨W, hWcyc, hWcard, hWcent, hWnorm, hWτ, hWsr⟩ :=
    transport_singer e (singerSubgroup ε) (2 ^ n + 1) (2 * (2 ^ n + 1))
      (isCyclic_singerSubgroup hε) hcard (centralizer_singerSubgroup hε) hnorm
      ⟨frobSL ε, frobSL_mul_self ε, fun v hv => by
        rw [frobSL_inv]
        exact frobSL_mul_mem_mul_frobSL hε hv⟩
  refine ⟨W, hWcyc, hWcard, hWcent, hWnorm, ?_, hWsr⟩
  obtain ⟨τ, hτ2, hτinv⟩ := hWτ
  exact ⟨τ, hτ2, fun v hv => by
    calc τ * v * τ = τ * v * τ⁻¹ := by rw [inv_eq_of_mul_eq_one_right hτ2]
      _ = v⁻¹ := hτinv v hv⟩

end Work.ZassenhausSuzuki.SingerModelCycle
