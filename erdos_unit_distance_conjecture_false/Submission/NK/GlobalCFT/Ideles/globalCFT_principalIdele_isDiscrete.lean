import Mathlib
import Submission.NK.GlobalCFT.Idele

/-!
# The principal idèles are discrete

For a number field `K` the diagonal image `Kˣ → 𝕀 K` of the principal idèles is a *discrete*
subset of the idèle group `𝕀 K`.

The proof follows the classical argument of Neukirch (Algebraic Number Theory, Chapter II):
the set

`V = {x : 𝕀 K | x` is a local unit at every finite place and `‖x_w - 1‖ < 1/2` at every
archimedean place `w}`

is an open neighbourhood of `1`.  For `k ∈ Kˣ` with `principalIdele K k ∈ V` one has
`k - 1 ∈ 𝓞 K` (integrality at all finite places) and `w (k - 1) < 1/2` at all archimedean
places; the norm `N(k - 1)` is then an integer of absolute value `< 1`, whence `k = 1`.  Thus
`V ∩ Kˣ = {1}`, and discreteness follows by translating `V` along the group.

## Main result

* `NK.GlobalCFT.Ideles.globalCFT_principalIdele_isDiscrete`
-/

set_option autoImplicit false

open scoped NumberField RestrictedProduct

open NumberField IsDedekindDomain

noncomputable section

namespace NK.GlobalCFT.Ideles

variable {K : Type*} [Field K] [NumberField K]

/-- **The norm on an archimedean completion is the archimedean absolute value.**  For an infinite
place `w` of `K` and `x : K`, the norm of the image of `x` in the local field `K_w` is `w x`.
This is the compatibility between the local norm of the completion and the (global) place `w`
that makes the product formula usable in the local computations below. -/
private theorem norm_algebraMap_localField_ofInfinite (w : InfinitePlace K) (x : K) :
    ‖algebraMap K (Place.localField K (Place.ofInfinite w)) x‖ = w x := by
  change ‖algebraMap K (NumberField.InfinitePlace.Completion w) x‖ = w x
  rw [NumberField.InfinitePlace.Completion.algebraMap_apply,
    NumberField.InfinitePlace.Completion.norm_coe]
  simp

/-- If the principal idèle `k` is a local unit at a finite place `q`, then `k - 1` is integral
at `q`.

Indeed `k` then has `q`-adic valuation exactly `1`, and the valuation of `k - 1 = k + (-1)` is
bounded by the maximum of the valuations of `k` and of `-1`, both of which are `1`. -/
private theorem valuation_sub_le_one_of_mem_localUnits {k : Kˣ}
    {q : HeightOneSpectrum (𝓞 K)}
    (h : NK.GlobalCFT.Idele.principalIdele K k (Place.ofFinite q) ∈
      Place.localUnits K (Place.ofFinite q)) :
    q.valuation K ((k : K) - 1) ≤ 1 := by
  have h' : Valued.v (R := q.adicCompletion K)
      (algebraMap K (q.adicCompletion K) (k : K)) = 1 := by
    have := (Place.mem_localUnits_ofFinite_iff_valued_eq_one (K := K) (q := q)
      (x := Units.map (algebraMap K (q.adicCompletion K)) k)).mp (by
        simpa [Place.localUnits_ofFinite, NK.GlobalCFT.Idele.principalIdele_apply] using h)
    simpa using this
  have hk : q.valuation K (k : K) = 1 := by
    rw [← Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq q (k : K)]
    exact h'
  calc q.valuation K ((k : K) - 1)
      ≤ max (q.valuation K (k : K)) (q.valuation K 1) := Valuation.map_sub _ _ _
    _ = 1 := by rw [hk, map_one, max_self]

/-- The archimedean coordinates of the principal idèle `k` being close to `1` means that
`w (k - 1) < 1/2` for every infinite place `w`. -/
private theorem apply_sub_lt_of_norm_sub_lt {k : Kˣ} (w : InfinitePlace K)
    (h : ‖(((NK.GlobalCFT.Idele.principalIdele K k (Place.ofInfinite w) :
        (Place.localField K (Place.ofInfinite w))ˣ) :
          Place.localField K (Place.ofInfinite w)) - 1)‖ < 1 / 2) :
    w ((k : K) - 1) < 1 / 2 := by
  have key : ‖algebraMap K (Place.localField K (Place.ofInfinite w)) ((k : K) - 1)‖ =
      w ((k : K) - 1) := norm_algebraMap_localField_ofInfinite w _
  have hid : (((NK.GlobalCFT.Idele.principalIdele K k (Place.ofInfinite w) :
        (Place.localField K (Place.ofInfinite w))ˣ) :
          Place.localField K (Place.ofInfinite w)) - 1)
      = algebraMap K (Place.localField K (Place.ofInfinite w)) ((k : K) - 1) := by
    rw [NK.GlobalCFT.Idele.principalIdele_apply]
    change (algebraMap K (Place.localField K (Place.ofInfinite w)) (k : K) - 1) = _
    rw [map_sub, map_one]
  rw [hid, key] at h
  exact h

/-- The set of idèles which are local units at every finite place and whose archimedean
coordinates are within distance `1/2` of `1`: an open neighbourhood of `1` meeting the
principal idèles only in `1`. -/
def principalNhd (K : Type*) [Field K] [NumberField K] :
    Set (NK.GlobalCFT.Idele K) :=
  {x | ∀ v : Place K, Place.IsFinite v → x v ∈ Place.localUnits K v} ∩
    (⋂ w : InfinitePlace K,
      {x | ‖(((x (Place.ofInfinite w) : (Place.localField K (Place.ofInfinite w))ˣ) :
          Place.localField K (Place.ofInfinite w)) - 1)‖ < 1 / 2})

theorem mem_principalNhd {x : NK.GlobalCFT.Idele K} :
    x ∈ principalNhd K ↔
      (∀ v : Place K, Place.IsFinite v → x v ∈ Place.localUnits K v) ∧
        ∀ w : InfinitePlace K,
          ‖(((x (Place.ofInfinite w) : (Place.localField K (Place.ofInfinite w))ˣ) :
              Place.localField K (Place.ofInfinite w)) - 1)‖ < 1 / 2 := by
  simp [principalNhd]

/-- The continuity of the archimedean coordinates of an idèle, as a map into the local field. -/
private theorem continuous_val_ofInfinite (w : InfinitePlace K) :
    Continuous (fun x : NK.GlobalCFT.Idele K =>
      ((x (Place.ofInfinite w) : (Place.localField K (Place.ofInfinite w))ˣ) :
        Place.localField K (Place.ofInfinite w))) := by
  have h : Continuous (fun x : Πʳ v : Place K,
      [(Place.localField K v)ˣ, (Place.localUnits K v : Set _)] =>
      ((x (Place.ofInfinite w) : (Place.localField K (Place.ofInfinite w))ˣ) :
        Place.localField K (Place.ofInfinite w))) := by
    simpa [Function.comp_def] using Units.continuous_val.comp
      (RestrictedProduct.continuous_eval (R := fun v : Place K => (Place.localField K v)ˣ)
        (A := fun v : Place K => (Place.localUnits K v : Set _)) (Place.ofInfinite w))
  exact h

theorem isOpen_principalNhd : IsOpen (principalNhd K) := by
  have hfin : IsOpen {x : NK.GlobalCFT.Idele K |
      ∀ v : Place K, Place.IsFinite v → x v ∈ Place.localUnits K v} := by
    have h := RestrictedProduct.isOpen_forall_imp_mem
      (R := fun v : Place K => (Place.localField K v)ˣ)
      (A := fun v : Place K => (Place.localUnits K v : Set _))
      (p := fun v => Place.IsFinite v) (fun v => Place.isOpen_localUnits v)
    exact h
  refine hfin.inter ?_
  refine isOpen_iInter_of_finite fun w => ?_
  apply isOpen_lt _ continuous_const
  exact continuous_norm.comp ((continuous_val_ofInfinite w).sub continuous_const)

theorem one_mem_principalNhd : (1 : NK.GlobalCFT.Idele K) ∈ principalNhd K := by
  rw [mem_principalNhd]
  refine ⟨fun v _ => Subgroup.one_mem _, fun w => ?_⟩
  have h1 : (1 : NK.GlobalCFT.Idele K) (Place.ofInfinite w) = 1 := rfl
  rw [h1]
  norm_num

/-- **A principal idèle in the neighbourhood `V` is trivial.** -/
private theorem eq_one_of_mem_principalNhd (k : Kˣ)
    (hfin : ∀ q : HeightOneSpectrum (𝓞 K),
      NK.GlobalCFT.Idele.principalIdele K k (Place.ofFinite q) ∈
        Place.localUnits K (Place.ofFinite q))
    (hinf : ∀ w : InfinitePlace K,
      ‖(((NK.GlobalCFT.Idele.principalIdele K k (Place.ofInfinite w) :
          (Place.localField K (Place.ofInfinite w))ˣ) :
            Place.localField K (Place.ofInfinite w)) - 1)‖ < 1 / 2) :
    k = 1 := by
  -- integrality of `k - 1` at every finite place
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 K, (x : K) = (k : K) - 1 :=
    IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one K ((k : K) - 1)
      (fun q => valuation_sub_le_one_of_mem_localUnits (hfin q))
  -- archimedean bound on the norm
  have hboundR : ((|Algebra.norm ℚ ((k : K) - 1)| : ℚ) : ℝ) < 1 := by
    rw [← NumberField.InfinitePlace.prod_eq_abs_norm ((k : K) - 1)]
    have hle : ∏ w : InfinitePlace K,
        (w ((k : K) - 1)) ^ (NumberField.InfinitePlace.mult w) ≤
        (1 / 2 : ℝ) ^ (Module.finrank ℚ K) := by
      calc ∏ w : InfinitePlace K,
            (w ((k : K) - 1)) ^ (NumberField.InfinitePlace.mult w)
          ≤ ∏ w : InfinitePlace K,
              (1 / 2 : ℝ) ^ (NumberField.InfinitePlace.mult w) := by
            refine Finset.prod_le_prod₀ (fun w _ => ?_) (fun w _ => ?_)
            · exact pow_nonneg (w.1.nonneg _) _
            · exact pow_le_pow_left₀ (w.1.nonneg _)
                (le_of_lt (apply_sub_lt_of_norm_sub_lt w (hinf w))) _
        _ = (1 / 2 : ℝ) ^ (∑ w : InfinitePlace K, NumberField.InfinitePlace.mult w) :=
            Finset.prod_pow_eq_pow_sum _ _ _
        _ = (1 / 2 : ℝ) ^ (Module.finrank ℚ K) := by
            rw [NumberField.InfinitePlace.sum_mult_eq]
    have hd : (1 / 2 : ℝ) ^ (Module.finrank ℚ K) ≤ 1 / 2 := by
      have h1 : 1 ≤ Module.finrank ℚ K := Module.finrank_pos
      have := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) h1
      simpa using this
    linarith
  -- `N(k-1)` is a rational integer
  have hN : Algebra.norm ℚ ((k : K) - 1) = ((Algebra.norm ℤ x : ℤ) : ℚ) := by
    rw [← hx, Algebra.coe_norm_int]
  have hz : Algebra.norm ℤ x = 0 := by
    have h1q : |((Algebra.norm ℤ x : ℤ) : ℚ)| < 1 := by
      rw [← hN]
      exact_mod_cast hboundR
    have h2 : ((|Algebra.norm ℤ x| : ℤ) : ℚ) < 1 := by
      rw [Int.cast_abs]
      exact h1q
    have h3 : |Algebra.norm ℤ x| < 1 := by exact_mod_cast h2
    exact Int.abs_lt_one_iff.mp h3
  have hnorm0 : Algebra.norm ℚ ((k : K) - 1) = 0 := by
    rw [hN, hz, Int.cast_zero]
  have hsub : (k : K) - 1 = 0 := Algebra.norm_eq_zero_iff.mp hnorm0
  exact Units.ext (sub_eq_zero.mp hsub)

theorem globalCFT_principalIdele_isDiscrete {K : Type*} [Field K] [NumberField K] :
    IsDiscrete (Set.range (NK.GlobalCFT.Idele.principalIdele K)) := by
  rw [isDiscrete_iff_forall_mem_exists_isOpen]
  rintro y ⟨k, rfl⟩
  refine ⟨{x : NK.GlobalCFT.Idele K |
      (NK.GlobalCFT.Idele.principalIdele K k)⁻¹ * x ∈ principalNhd K},
    (isOpen_principalNhd.preimage (continuous_const.mul continuous_id)), ?_⟩
  ext z
  constructor
  · rintro ⟨hzA, ⟨j, rfl⟩⟩
    have hz' : NK.GlobalCFT.Idele.principalIdele K (k⁻¹ * j) ∈ principalNhd K := by
      simpa [map_mul] using hzA
    have hj : k⁻¹ * j = 1 :=
      eq_one_of_mem_principalNhd (k⁻¹ * j) (fun q => (mem_principalNhd.mp hz').1 _ (by simp))
        (fun w => (mem_principalNhd.mp hz').2 w)
    have hjk : j = k := by
      have h := congrArg (fun u : Kˣ => k * u) hj
      simpa using h
    rw [hjk]
    exact Set.mem_singleton _
  · intro hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨?_, ⟨k, rfl⟩⟩
    simpa using one_mem_principalNhd (K := K)

end NK.GlobalCFT.Ideles
