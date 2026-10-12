import Mathlib.RingTheory.PicardGroup
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.BoseBoxFock.Defs
import Submission.Work.BoseBoxFock.eFunMemLp
import Submission.Work.BoseBoxFock.eFunOrthonormal
import Submission.Work.BoseBoxFock.integralStarEFunMul
import Submission.Work.BoseBoxFock.orthonormalComplex
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.exists_boxOrthFam` — an orthonormal family in the box, orthogonal to `v`

The box `Λ(ℓ) = boxL ℓ = ℓ • unitCell` has volume `ℓ³ > 0`, and its `L²` space is
infinite-dimensional: `BoxOrthDefs` cuts `Λ(ℓ)` into `N` disjoint slabs

`eSlice ℓ N k = {x | x 0 ∈ [a k, a (k+1)), |x 1| ≤ ℓ/2, |x 2| ≤ ℓ/2}`,  `a k = -ℓ/2 + k·(ℓ/N)`

of volume `ℓ³/N`, with normalised indicators `eFun ℓ N k` (`k : Fin N`, `N ≥ 1`) which
form an orthonormal family in `L²(volume)` (`eFunOrthonormal`) of bounded functions
supported in the box (`eFunMemLp`, `eSlice_subset_boxL`).

Taking `N = m + #ι + 1` slabs, the linear system

`d ↦ (i ↦ Σ_k d_k ∫_{eSlice k} v i)`      (`slabMap ℓ N v`)

maps `ℂ^N` to `ℂ^ι`, so its kernel has dimension at least `N - #ι ≥ m`; by
`orthonormalComplex` there are `d_1,…,d_m` orthonormal in that kernel.  The family

`b t = Σ_k conj(d t k) · eFun ℓ N k`

then is bounded, `L²`, supported in the box, orthonormal
(`∫ conj(b t) b t' = Σ_k d t k conj(d t' k) = conj ⟪d t, d t'⟫ = δ_{t,t'}`), and
orthogonal to every `v i`:

`∫ conj(b t) · v i = Σ_k d t k ∫ conj(eFun k)·v i = slScale · Σ_k d t k ∫_{eSlice k} v i
 = slScale · (slabMap ℓ N v (d t)) i = 0`.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Work.BoseBoxFock

/-- **The slab-integral system**: `d ↦ (i ↦ Σ_k d_k ∫_{slab k} v i)`, a `ℂ`-linear map
`ℂ^N → ℂ^ι`.  Its kernel consists of the coefficient vectors whose slab combination is
orthogonal to every `v i`. -/
def slabMap (ℓ : ℝ) (N : ℕ) {ι : Type*} (v : ι → EuclideanSpace ℝ (Fin 3) → ℂ) :
    EuclideanSpace ℂ (Fin N) →ₗ[ℂ] (ι → ℂ) where
  toFun d i := ∑ k : Fin N, d k * ∫ x in eSlice ℓ N k, v i x
  map_add' a b := by
    ext i
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [PiLp.add_apply]
    ring
  map_smul' c a := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring

@[simp] lemma slabMap_apply (ℓ : ℝ) (N : ℕ) {ι : Type*} (v : ι → EuclideanSpace ℝ (Fin 3) → ℂ)
    (d : EuclideanSpace ℂ (Fin N)) (i : ι) :
    slabMap ℓ N v d i = ∑ k : Fin N, d k * ∫ x in eSlice ℓ N k, v i x := rfl

/-- The product of the two slab combinations expands as a double sum. -/
private lemma star_sum_mul_sum (ℓ : ℝ) {N : ℕ} {m : ℕ}
    (e : Fin m → EuclideanSpace ℂ (Fin N)) (t t' : Fin m)
    (x : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) (∑ k : Fin N, (starRingEnd ℂ) (e t k) * eFun ℓ N k x)
        * (∑ l : Fin N, (starRingEnd ℂ) (e t' l) * eFun ℓ N l x)
      = ∑ k : Fin N, ∑ l : Fin N, ((e t k) * (starRingEnd ℂ) (e t' l))
          * ((starRingEnd ℂ) (eFun ℓ N k x) * eFun ℓ N l x) := by
  rw [starRingEnd_apply, star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [starRingEnd_apply, star_mul, star_star]
  ring

/-- The `star` of a slab combination, multiplied by a test function, as a single sum. -/
private lemma star_sum_mul (ℓ : ℝ) {N : ℕ} {m : ℕ}
    (e : Fin m → EuclideanSpace ℂ (Fin N)) (t : Fin m)
    (w : EuclideanSpace ℝ (Fin 3) → ℂ) (x : EuclideanSpace ℝ (Fin 3)) :
    (starRingEnd ℂ) (∑ k : Fin N, (starRingEnd ℂ) (e t k) * eFun ℓ N k x) * w x
      = ∑ k : Fin N, (e t k) * ((starRingEnd ℂ) (eFun ℓ N k x) * w x) := by
  rw [starRingEnd_apply, star_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [starRingEnd_apply, star_mul, star_star]
  ring

theorem exists_boxOrthFam (ℓ : ℝ) (hℓ : 0 < ℓ) {ι : Type*} [Fintype ι]
    (v : ι → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hv : ∀ i, MeasureTheory.MemLp (v i) 2
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (m : ℕ) :
    ∃ b : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ,
      (∀ t, MeasureTheory.MemLp (b t) ⊤
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ t, MeasureTheory.MemLp (b t) 2
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) ∧
      (∀ t, Function.support (b t) ⊆ Work.BoseK15.corpusBox.boxL ℓ) ∧
      (∀ t t', (∫ x, (starRingEnd ℂ) (b t x) * b t' x) = if t = t' then 1 else 0) ∧
      (∀ t i, (∫ x, (starRingEnd ℂ) (b t x) * v i x) = 0) := by
  classical
  -- the number of slabs
  set N : ℕ := m + Fintype.card ι + 1 with hNdef
  have hNpos : 0 < N := by omega
  -- the slab-integral system and its kernel
  have hdim : m ≤ Module.finrank ℂ ↥(LinearMap.ker (slabMap (ι := ι) ℓ N v)) := by
    have hrank := LinearMap.finrank_range_add_finrank_ker (slabMap (ι := ι) ℓ N v)
    have hrange : Module.finrank ℂ ↥(LinearMap.range (slabMap (ι := ι) ℓ N v))
        ≤ Fintype.card ι := by
      have h := Submodule.finrank_le (LinearMap.range (slabMap (ι := ι) ℓ N v))
      rwa [Module.finrank_fintype_fun_eq_card] at h
    have hdom : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = N := by simp
    omega
  obtain ⟨e, heOrth, heMem⟩ :=
    orthonormalComplex (LinearMap.ker (slabMap (ι := ι) ℓ N v)) hdim
  have hek : ∀ t : Fin m, slabMap (ι := ι) ℓ N v (e t) = 0 := fun t =>
    LinearMap.mem_ker.mp (heMem t)
  refine ⟨fun t x => ∑ k : Fin N, (starRingEnd ℂ) (e t k) * eFun ℓ N k x, ?_, ?_, ?_, ?_, ?_⟩
  · -- `L^∞`
    intro t
    exact memLp_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (p := (⊤ : ℝ≥0∞)) (s := Finset.univ)
      (f := fun k x => (starRingEnd ℂ) (e t k) * eFun ℓ N k x)
      (fun k _ => (eFunMemLp ℓ hℓ N hNpos k).1.const_mul (starRingEnd ℂ (e t k)))
  · -- `L²`
    intro t
    exact memLp_finsetSum (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      (p := (2 : ℝ≥0∞)) (s := Finset.univ)
      (f := fun k x => (starRingEnd ℂ) (e t k) * eFun ℓ N k x)
      (fun k _ => (eFunMemLp ℓ hℓ N hNpos k).2.const_mul (starRingEnd ℂ (e t k)))
  · -- support in the box
    intro t x hx
    change (∑ k : Fin N, (starRingEnd ℂ) (e t k) * eFun ℓ N k x) ≠ 0 at hx
    by_contra hxb
    exact hx (Finset.sum_eq_zero fun k _ => by
      rw [eFun_of_notMem (fun hc => hxb (eSlice_subset_boxL hℓ hNpos k hc)), mul_zero])
  · -- orthonormality
    intro t t'
    have hint : ∀ k l : Fin N,
        Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
          (starRingEnd ℂ) (eFun ℓ N k x) * eFun ℓ N l x)
          (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
      fun k l => (eFunOrthonormal ℓ hℓ N hNpos k l).1
    have h2 : (∫ x, (starRingEnd ℂ) (∑ k : Fin N, (starRingEnd ℂ) (e t k) * eFun ℓ N k x)
          * (∑ l : Fin N, (starRingEnd ℂ) (e t' l) * eFun ℓ N l x))
        = ∑ k : Fin N, ∑ l : Fin N, ((e t k) * (starRingEnd ℂ) (e t' l))
            * (∫ x, (starRingEnd ℂ) (eFun ℓ N k x) * eFun ℓ N l x) := by
      rw [show (∫ x, (starRingEnd ℂ) (∑ k : Fin N, (starRingEnd ℂ) (e t k) * eFun ℓ N k x)
            * (∑ l : Fin N, (starRingEnd ℂ) (e t' l) * eFun ℓ N l x))
          = ∫ x, ∑ k : Fin N, ∑ l : Fin N, ((e t k) * (starRingEnd ℂ) (e t' l))
              * ((starRingEnd ℂ) (eFun ℓ N k x) * eFun ℓ N l x) from
        integral_congr_ae (Filter.Eventually.of_forall fun x => star_sum_mul_sum ℓ e t t' x)]
      rw [integral_finsetSum Finset.univ
        (f := fun k x => ∑ l : Fin N, ((e t k) * (starRingEnd ℂ) (e t' l))
          * ((starRingEnd ℂ) (eFun ℓ N k x) * eFun ℓ N l x))]
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_finsetSum Finset.univ
          (f := fun l x => ((e t k) * (starRingEnd ℂ) (e t' l))
            * ((starRingEnd ℂ) (eFun ℓ N k x) * eFun ℓ N l x))]
        · exact Finset.sum_congr rfl fun l _ => by rw [integral_const_mul]
        · intro l _
          exact (hint k l).const_mul _
      · intro k _
        exact integrable_finsetSum Finset.univ fun l _ => (hint k l).const_mul _
    rw [h2]
    have h3 : ∀ k : Fin N, (∫ x, (starRingEnd ℂ) (eFun ℓ N k x) * eFun ℓ N k x) = 1 :=
      fun k => by simpa using (eFunOrthonormal ℓ hℓ N hNpos k k).2
    have h4 : ∀ k l : Fin N, k ≠ l →
        (∫ x, (starRingEnd ℂ) (eFun ℓ N k x) * eFun ℓ N l x) = 0 := fun k l hkl => by
      simpa [hkl] using (eFunOrthonormal ℓ hℓ N hNpos k l).2
    have h5 : (∑ k : Fin N, ∑ l : Fin N, ((e t k) * (starRingEnd ℂ) (e t' l))
          * (∫ x, (starRingEnd ℂ) (eFun ℓ N k x) * eFun ℓ N l x))
        = ∑ k : Fin N, (e t k) * (starRingEnd ℂ) (e t' k) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      refine (Finset.sum_eq_single k ?_ ?_).trans ?_
      · intro l _ hl
        rw [h4 k l (Ne.symm hl), mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
      · rw [h3 k, mul_one]
    rw [h5]
    have h6 : (∑ k : Fin N, (e t k) * (starRingEnd ℂ) (e t' k))
        = (starRingEnd ℂ) (inner ℂ (e t) (e t')) := by
      have hinner : inner ℂ (e t) (e t') = ∑ k : Fin N, star (e t k) * e t' k := by
        simp only [PiLp.inner_apply, RCLike.inner_apply]
        exact Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [hinner, map_sum]
      exact Finset.sum_congr rfl fun k _ => by
        simp only [starRingEnd_apply, star_mul, star_star]
        ring
    rw [h6, show inner ℂ (e t) (e t') = (if t = t' then 1 else 0) from
      (orthonormal_iff_ite.mp heOrth) t t']
    by_cases h : t = t' <;> simp [h]
  · -- orthogonality to the `v i`
    intro t i
    have hint : ∀ k : Fin N,
        Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
          (starRingEnd ℂ) (eFun ℓ N k x) * v i x)
          (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
      fun k => (integralStarEFunMul ℓ hℓ N hNpos k (v i) (hv i)).1
    have h2 : (∫ x, (starRingEnd ℂ) (∑ k : Fin N, (starRingEnd ℂ) (e t k) * eFun ℓ N k x)
          * v i x)
        = ∑ k : Fin N, (e t k) * (∫ x, (starRingEnd ℂ) (eFun ℓ N k x) * v i x) := by
      rw [show (∫ x, (starRingEnd ℂ) (∑ k : Fin N, (starRingEnd ℂ) (e t k) * eFun ℓ N k x)
            * v i x)
          = ∫ x, ∑ k : Fin N, (e t k)
              * ((starRingEnd ℂ) (eFun ℓ N k x) * v i x) from
        integral_congr_ae (Filter.Eventually.of_forall fun x => star_sum_mul ℓ e t (v i) x)]
      rw [integral_finsetSum Finset.univ
        (f := fun k x => (e t k) * ((starRingEnd ℂ) (eFun ℓ N k x) * v i x))]
      · exact Finset.sum_congr rfl fun k _ => by rw [integral_const_mul]
      · intro k _
        exact (hint k).const_mul _
    rw [h2]
    have h3 : (∑ k : Fin N, (e t k) * (∫ x, (starRingEnd ℂ) (eFun ℓ N k x) * v i x))
        = ((slScale ℓ N : ℝ) : ℂ) * (slabMap (ι := ι) ℓ N v (e t) i) := by
      rw [slabMap_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [(integralStarEFunMul ℓ hℓ N hNpos k (v i) (hv i)).2]
      ring
    rw [h3, hek t]
    simp

end Work.BoseBoxFock
