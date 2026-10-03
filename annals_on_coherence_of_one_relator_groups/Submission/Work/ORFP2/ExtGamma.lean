/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The class of a kernel element in the relation module, and the key lemma

For `φ : FreeGroup (Fin n) →* G` surjective we push the Fox derivative of `m : F` forward along
`k[F] → k[G]`, obtaining `foxGamma m ∈ relationModule k G φ` for `m ∈ ker φ`.  The main result
is that every element of the relation module is a `k[G]`-linear combination of these classes
("key lemma").
-/
import Mathlib
import Submission.Work.ORFP2.ExtFox

set_option autoImplicit false

namespace Work.ORFP2.Ext

open MonoidAlgebra

variable (k : Type*) [CommRing k] {n : ℕ} {G : Type*} [Group G]

section Push

variable (φ : FreeGroup (Fin n) →* G)

/-- Push the coefficients of `Fin n →₀ k[F]` forward along the algebra map induced by `φ`. -/
noncomputable def foxPush (c : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    Fin n →₀ MonoidAlgebra k G :=
  c.mapRange (phiAlg k φ) (map_zero _)

lemma foxPush_single (i : Fin n) (r : MonoidAlgebra k (FreeGroup (Fin n))) :
    foxPush k φ (Finsupp.single i r) = Finsupp.single i (phiAlg k φ r) :=
  Finsupp.mapRange_single

lemma foxPush_add (c d : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    foxPush k φ (c + d) = foxPush k φ c + foxPush k φ d :=
  Finsupp.mapRange_add (fun x y => map_add (phiAlg k φ) x y) c d

lemma foxPush_zero : foxPush k φ (0 : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) = 0 :=
  Finsupp.mapRange_zero

lemma foxPush_smul (a : MonoidAlgebra k (FreeGroup (Fin n)))
    (c : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    foxPush k φ (a • c) = (phiAlg k φ a) • foxPush k φ c :=
  Finsupp.mapRange_smul' a (phiAlg k φ a) c (fun x => by simp only [smul_eq_mul, map_mul])

lemma foxPush_sum (c : ↥(φ.ker) →₀ MonoidAlgebra k (FreeGroup (Fin n)))
    (g : ↥(φ.ker) → MonoidAlgebra k (FreeGroup (Fin n)) →
      Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    foxPush k φ (c.sum g) = c.sum (fun r a => foxPush k φ (g r a)) := by
  change (Finsupp.mapRange.addMonoidHom ((phiAlg k φ).toRingHom.toAddMonoidHom)) (c.sum g)
    = c.sum (fun r a =>
      (Finsupp.mapRange.addMonoidHom ((phiAlg k φ).toRingHom.toAddMonoidHom)) (g r a))
  exact map_finsuppSum _ c g

lemma phiAlg_surjective (hφ : Function.Surjective φ) : Function.Surjective (phiAlg k φ) := by
  intro b
  have hb : b = ∑ g ∈ b.coeff.support,
      b.coeff g • (MonoidAlgebra.single g (1 : k) : MonoidAlgebra k G) :=
    Work.ORFP2.eq_sum_smul_single k G b
  refine ⟨∑ g ∈ b.coeff.support,
    b.coeff g • (MonoidAlgebra.single (sec φ hφ g) (1 : k) :
      MonoidAlgebra k (FreeGroup (Fin n))), ?_⟩
  rw [map_sum]
  conv_rhs => rw [hb]
  apply Finset.sum_congr rfl
  intro g _
  rw [map_smul, phiAlg_single, phi_sec]

/-- Lifting an element of `k[G]` to `k[F]` along a splitting of `φ`, sending `0` to `0`. -/
noncomputable def liftAlg (hφ : Function.Surjective φ) (b : MonoidAlgebra k G) :
    MonoidAlgebra k (FreeGroup (Fin n)) := by
  classical
  exact if b = 0 then 0 else Function.surjInv (phiAlg_surjective k φ hφ) b

lemma phiAlg_liftAlg (hφ : Function.Surjective φ) (b : MonoidAlgebra k G) :
    phiAlg k φ (liftAlg k φ hφ b) = b := by
  classical
  unfold liftAlg
  split_ifs with h
  · rw [h, map_zero]
  · exact Function.surjInv_eq (phiAlg_surjective k φ hφ) b

lemma liftAlg_zero (hφ : Function.Surjective φ) :
    liftAlg k φ hφ (0 : MonoidAlgebra k G) = 0 := by
  classical
  simp only [liftAlg, if_true]

lemma foxPush_surjective (hφ : Function.Surjective φ) : Function.Surjective (foxPush k φ) := by
  intro y
  refine ⟨y.mapRange (liftAlg k φ hφ) (liftAlg_zero k φ hφ), ?_⟩
  rw [foxPush, Finsupp.mapRange_mapRange]
  ext i
  rw [Finsupp.mapRange_apply, Function.comp_apply, phiAlg_liftAlg]

end Push

section Gamma

variable (hbasis : FreeGroupAugIdealBasis k) (n : ℕ) (φ : FreeGroup (Fin n) →* G)

/-- The push-forward of the Fox derivative of `m : F`, an element of `k[G]ⁿ`. -/
noncomputable def foxGamma (m : FreeGroup (Fin n)) : Fin n →₀ MonoidAlgebra k G :=
  foxPush k φ (foxDelta k hbasis n m)

lemma foxGamma_push (m : FreeGroup (Fin n)) :
    foxGamma k hbasis n φ m = foxPush k φ (foxDelta k hbasis n m) := rfl

lemma relMap_foxPush (w : Fin n →₀ MonoidAlgebra k (FreeGroup (Fin n))) :
    relMap k G φ (foxPush k φ w) = phiAlg k φ (foxLambda k n w) := by
  induction w using Finsupp.induction_linear with
  | zero => rw [foxPush_zero, map_zero (foxLambda k n), map_zero (relMap k G φ),
      map_zero (phiAlg k φ)]
  | add p q hp hq =>
      rw [foxPush_add, map_add, LinearMap.map_add (foxLambda k n), map_add, hp, hq]
  | single i r =>
      rw [foxPush_single, relMap, Finsupp.linearCombination_single, foxLambda,
        Finsupp.linearCombination_single]
      conv_rhs => rw [smul_eq_mul, map_mul, map_sub, map_one (phiAlg k φ), phiAlg_single]
      rw [smul_eq_mul]

lemma foxGamma_mem (m : FreeGroup (Fin n)) (hm : m ∈ MonoidHom.ker φ) :
    foxGamma k hbasis n φ m ∈ relationModule k G φ := by
  rw [relationModule, LinearMap.mem_ker, foxGamma_push, relMap_foxPush, foxLambda_foxDelta,
    map_sub, phiAlg_single, MonoidHom.mem_ker.mp hm, map_one]
  rw [show (MonoidAlgebra.single (1 : G) (1 : k) : MonoidAlgebra k G) = 1 from
    MonoidAlgebra.one_def.symm, sub_self]

lemma foxGamma_one : foxGamma k hbasis n φ 1 = 0 := by
  rw [foxGamma_push, foxDelta_one, foxPush_zero]

lemma foxGamma_mul (a b : FreeGroup (Fin n)) :
    foxGamma k hbasis n φ (a * b) =
      (MonoidAlgebra.single (φ a) (1 : k)) • foxGamma k hbasis n φ b
        + foxGamma k hbasis n φ a := by
  rw [foxGamma_push, foxDelta_mul, foxPush_add, foxPush_smul, phiAlg_single,
    foxGamma_push, foxGamma_push]

lemma foxGamma_add {a b : FreeGroup (Fin n)} (ha : a ∈ MonoidHom.ker φ)
    (hb : b ∈ MonoidHom.ker φ) :
    foxGamma k hbasis n φ (a * b) = foxGamma k hbasis n φ a + foxGamma k hbasis n φ b := by
  rw [foxGamma_mul, MonoidHom.mem_ker.mp ha, MonoidAlgebra.one_def.symm, one_smul, add_comm]

lemma single_phi_smul_foxGamma_inv (g : FreeGroup (Fin n)) :
    (MonoidAlgebra.single (φ g) (1 : k)) • foxGamma k hbasis n φ g⁻¹
      = -foxGamma k hbasis n φ g := by
  have h := foxGamma_mul k hbasis n φ g g⁻¹
  rw [mul_inv_cancel, foxGamma_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

lemma foxGamma_conj (g m : FreeGroup (Fin n)) (hm : m ∈ MonoidHom.ker φ) :
    foxGamma k hbasis n φ (g * m * g⁻¹)
      = (MonoidAlgebra.single (φ g) (1 : k)) • foxGamma k hbasis n φ m := by
  rw [show g * m * g⁻¹ = g * (m * g⁻¹) from by group, foxGamma_mul, foxGamma_mul,
    MonoidHom.mem_ker.mp hm, MonoidAlgebra.one_def.symm, one_smul, smul_add,
    single_phi_smul_foxGamma_inv]
  abel

/-- **Key lemma.**  Every element of the relation module is a `k[G]`-linear combination of the
elements `foxGamma r`, `r ∈ ker φ`. -/
theorem relationModule_eq_span_foxGamma (hφ : Function.Surjective φ)
    (y : Fin n →₀ MonoidAlgebra k G) (hy : y ∈ relationModule k G φ) :
    ∃ c : ↥(φ.ker) →₀ MonoidAlgebra k G,
      y = c.sum (fun r b => b • foxGamma k hbasis n φ r) := by
  obtain ⟨w, hw⟩ := foxPush_surjective k φ hφ y
  have hz0 : phiAlg k φ (foxLambda k n w) = 0 := by
    rw [← relMap_foxPush k n φ, hw]
    exact LinearMap.mem_ker.mp hy
  obtain ⟨c, hc⟩ : foxLambda k n w ∈ LinearMap.range (comb k φ) := by
    rw [range_comb]
    exact (mem_JJ_iff k φ hφ _).mp (RingHom.mem_ker.mpr hz0)
  have hD : foxD k hbasis n (foxLambda k n w)
      = c.sum (fun r a => a • foxDelta k hbasis n (r : FreeGroup (Fin n))) := by
    rw [← hc, comb_apply, map_finsuppSum]
    exact Finsupp.sum_congr fun r _ => by
      rw [foxD_smul_augIdeal k hbasis n _
          ⟨MonoidAlgebra.single (r : FreeGroup (Fin n)) (1 : k) - 1,
            single_sub_one_mem_augIdeal k (FreeGroup (Fin n)) (r : FreeGroup (Fin n))⟩,
        foxD_sub_one]
  refine ⟨c.mapRange (phiAlg k φ) (map_zero _), ?_⟩
  rw [Finsupp.sum_mapRange_index (fun r => by rw [zero_smul])]
  rw [← hw, ← foxD_foxLambda k hbasis n w, hD, foxPush_sum]
  exact Finsupp.sum_congr fun r _ => by rw [foxPush_smul, ← foxGamma_push]

end Gamma

end Work.ORFP2.Ext
