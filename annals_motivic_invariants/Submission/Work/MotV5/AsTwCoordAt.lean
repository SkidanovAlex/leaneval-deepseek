import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotV5.asCoord_asTwCoord
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The AS-twisted coordinates at a prescribed root

`Work.MotV5.asTwCoord D g` is defined through the *chosen* root `asRoot g` of `X⁵ - X - g`.
For the naturality of the AS twist field under automorphisms of the base field `K = 𝕜(t)`
(and for the `℘`-invariance of the twist field) one needs the twisted coordinates for an
*arbitrary* root `w` of `X⁵ - X - g`, together with the fact that two different roots give the
same field `K(y) ⊆ K̄(E)` as long as their difference lies in `K = 𝕜(t)`.

## Contents

* `asRatio D i` — the Klein coordinate ratios `x_i = κ_i/κ_0` (the interpolation values);
* `asTwCoordAt D w j` — the twisted coordinate `y_j = -∑_i x_i ((w+i)^{4-j} - δ_{j0})` for an
  arbitrary `w : Om D` (definitionally equal to `asTwCoord D g j` at `w = asRoot g`);
* `asTwFieldAt D w` — the field `K(y_0, …, y_4)`;
* `interpPoly D w` — the interpolation polynomial `∑_j y_j T^j`, whose values at `w + i` are the
  Klein ratios (`asCoord_asTwCoordAt`, the identity `asCoord w y i = x_i` of
  `Work.MotV5.asInterp`), and whose behaviour under `T ↦ T + c` is recorded in
  `interpPoly_shift`.
-/

set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV5
noncomputable section

variable {𝕜 : Type} [Field 𝕜]

/-- The Klein coordinate ratios `x i = κ i / κ 0`: the values interpolated by the twisted
coordinates (the "Galois coordinates" of the twist). -/
def asRatio (D : Work.MotV.KleinData 𝕜) (i : Fin 5) : Work.MotV.Om D :=
  Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i / Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0

/-- The AS twisted coordinates for a prescribed root `w` of `X^5 - X - g`:
`y_j = -∑_i x_i ((w+i)^{4-j} - δ_{j,0})`.  For `w = asRoot g` this is `asTwCoord D g`
definitionally (`asTwCoord_eq`). -/
def asTwCoordAt (D : Work.MotV.KleinData 𝕜) (w : Work.MotV.Om D) (j : Fin 5) :
    Work.MotV.Om D :=
  -∑ i : Fin 5, asRatio D i *
    ((w + ((i : ℕ) : Work.MotV.Om D)) ^ (4 - (j : ℕ)) -
      (if (j : ℕ) = 0 then 1 else 0))

/-- The field generated over `K = RatFunc 𝕜` by the AS twisted coordinates at the root `w`. -/
def asTwFieldAt (D : Work.MotV.KleinData 𝕜) (w : Work.MotV.Om D) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
  IntermediateField.adjoin (RatFunc 𝕜) (Set.range (asTwCoordAt D w))

theorem asTwCoord_eq (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (j : Fin 5) :
    Work.MotV5.asTwCoord D g j =
      asTwCoordAt D (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g)) j := rfl

theorem asTwField_eq (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) :
    asTwistField D g =
      asTwFieldAt D (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g)) := rfl

variable [CharP 𝕜 5]

/-- **The interpolation identity at an arbitrary root.**  The twisted coordinates interpolate the
Klein ratios at the nodes `w + i`: `asCoord w y k = ∑_j y_j (w+k)^j = x_k`.  This is
`Work.MotV5.asInterp` with `R = Om D` (`charP_Om`). -/
theorem asCoord_asTwCoordAt (D : Work.MotV.KleinData 𝕜) (w : Work.MotV.Om D) (k : Fin 5) :
    Work.MotV.asCoord w (asTwCoordAt D w) k = asRatio D k := by
  haveI : CharP (Work.MotV.Om D) 5 := charP_Om 𝕜 D
  have h := asInterp (R := Work.MotV.Om D) w (asRatio D) k
  simpa only [Work.MotV.asCoord, asTwCoordAt, asRatio] using h

/-- The interpolation polynomial `∑_j y_j T^j` of the twisted coordinates at `w`. -/
def interpPoly (D : Work.MotV.KleinData 𝕜) (w : Work.MotV.Om D) :
    Polynomial (Work.MotV.Om D) :=
  ∑ j : Fin 5, Polynomial.C (asTwCoordAt D w j) * Polynomial.X ^ (j : ℕ)

theorem interpPoly_eval (D : Work.MotV.KleinData 𝕜) (w : Work.MotV.Om D) (i : Fin 5) :
    (interpPoly D w).eval (w + ((i : ℕ) : Work.MotV.Om D)) = asRatio D i := by
  have h : (interpPoly D w).eval (w + ((i : ℕ) : Work.MotV.Om D)) =
      Work.MotV.asCoord w (asTwCoordAt D w) i := by
    rw [interpPoly, Work.MotV.asCoord]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X]
  rw [h, asCoord_asTwCoordAt]

/-- The nodes `w + i` are distinct (the numerals `0, …, 4` are distinct in characteristic `5`). -/
theorem injective_node (D : Work.MotV.KleinData 𝕜) (w : Work.MotV.Om D) :
    Function.Injective (fun i : Fin 5 => w + ((i : ℕ) : Work.MotV.Om D)) := by
  haveI : CharP (Work.MotV.Om D) 5 := charP_Om 𝕜 D
  intro i k h
  have h' : (((i : ℕ) : Work.MotV.Om D)) = ((k : ℕ) : Work.MotV.Om D) := add_left_cancel h
  have h2 : ((((i : ℤ) - (k : ℤ)) : ℤ) : Work.MotV.Om D) = 0 := by
    push_cast
    rw [h', sub_self]
  have h3 : (5 : ℤ) ∣ ((i : ℤ) - (k : ℤ)) := (CharP.intCast_eq_zero_iff (Work.MotV.Om D) 5 _).mp h2
  obtain ⟨m, hm⟩ := h3
  have hi : (i : ℤ) < 5 := by exact_mod_cast i.isLt
  have hk : (k : ℤ) < 5 := by exact_mod_cast k.isLt
  have h0i : (0 : ℤ) ≤ (i : ℤ) := by simp
  have h0k : (0 : ℤ) ≤ (k : ℤ) := by simp
  have hm0 : m = 0 := by omega
  exact Fin.ext (by omega)

/-- The interpolation polynomial has degree `≤ 4` (coefficient-wise). -/
theorem interpPoly_natDegree_le (D : Work.MotV.KleinData 𝕜) (w : Work.MotV.Om D) :
    (interpPoly D w).natDegree ≤ 4 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [interpPoly, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (by omega)]
  first | refl_ring1 | ring

/-- **The shift identity.**  The interpolation polynomial of the root `w + u` is the shifted
interpolation polynomial of `w`: `P_w(T) = P_{w+u}(T + u)`.  Both sides have degree `≤ 4` and agree
on the five distinct nodes `w + i` (`interpPoly_eval`). -/
theorem interpPoly_shift (D : Work.MotV.KleinData 𝕜) (w u : Work.MotV.Om D) :
    interpPoly D w =
      (interpPoly D (w + u)).comp (Polynomial.X + Polynomial.C u) := by
  have hdeg : ((interpPoly D (w + u)).comp (Polynomial.X + Polynomial.C u)).natDegree ≤ 4 :=
    calc _ ≤ (interpPoly D (w + u)).natDegree * (Polynomial.X + Polynomial.C u).natDegree :=
          Polynomial.natDegree_comp_le
      _ = (interpPoly D (w + u)).natDegree * 1 := by rw [Polynomial.natDegree_X_add_C]
      _ ≤ 4 := by rw [mul_one]; exact interpPoly_natDegree_le D _
  refine Polynomial.eq_of_natDegree_lt_card_of_eval_eq _ _ (injective_node D w) ?_ ?_
  · intro i
    rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [show (w + ((i : ℕ) : Work.MotV.Om D)) + u =
        (w + u) + ((i : ℕ) : Work.MotV.Om D) from by ring]
    rw [interpPoly_eval, interpPoly_eval]
  · rw [Fintype.card_fin]
    exact max_lt (lt_of_le_of_lt (interpPoly_natDegree_le D w) (by norm_num))
      (lt_of_le_of_lt hdeg (by norm_num))

/-- The coefficient of `interpPoly` is the twisted coordinate. -/
theorem interpPoly_coeff (D : Work.MotV.KleinData 𝕜) (w : Work.MotV.Om D) (j : Fin 5) :
    (interpPoly D w).coeff (j : ℕ) = asTwCoordAt D w j := by
  rw [interpPoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro k _ hk
    have hne : ¬ ((j : ℕ) = (k : ℕ)) := fun h => hk (Fin.ext h).symm
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The coefficient formula for the shift.**  For a polynomial of degree `≤ 4` the coefficients
of `p.comp (X + C u)` are the triangular combinations of the coefficients of `p` with coefficients
`u^{k-j} * C(k,j)`. -/
theorem coeff_comp_X_add_C (D : Work.MotV.KleinData 𝕜) (p : Polynomial (Work.MotV.Om D))
    (hp : p.natDegree ≤ 4)
    (u : Work.MotV.Om D) (j : ℕ) :
    (p.comp (Polynomial.X + Polynomial.C u)).coeff j =
      ∑ k ∈ Finset.range 5,
        p.coeff k * (u ^ (k - j) * ((k.choose j : ℕ) : Work.MotV.Om D)) := by
  have hsub : p.support ⊆ Finset.range 5 := by
    intro x hx
    rw [Polynomial.mem_support_iff] at hx
    rw [Finset.mem_range]
    by_contra h
    exact hx (Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega)))
  rw [Polynomial.comp, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  · intro x _ hx
    have hx0 : p.coeff x = 0 := by
      by_contra h
      exact hx (Polynomial.mem_support_iff.mpr h)
    rw [Polynomial.coeff_C_mul, hx0, zero_mul]

/-- **Root independence of the AS twist field (shifts by elements of `K`), one direction.**  If `u`
is the image of an element of `K = RatFunc 𝕜`, then every twisted coordinate at the root `w` is a
`K`-linear combination of the twisted coordinates at the root `w + u`: the coefficients of the
triangular substitution `P_w(T) = P_{w+u}(T + u)` are `u^{k-j} * C(k,j)`, which lie in `K`. -/
theorem asTwFieldAt_le_of_mem_range (D : Work.MotV.KleinData 𝕜) (w : Work.MotV.Om D)
    (u₀ : RatFunc 𝕜) :
    asTwFieldAt D w ≤ asTwFieldAt D (w + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀) := by
  rw [asTwFieldAt, IntermediateField.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  have h := coeff_comp_X_add_C D (interpPoly D (w + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀))
    (interpPoly_natDegree_le D _) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀) (j : ℕ)
  rw [← interpPoly_shift D w (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀)] at h
  rw [interpPoly_coeff] at h
  rw [h]
  have hmem : ∀ k ∈ Finset.range 5,
      (interpPoly D (w + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀)).coeff k *
        ((algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀) ^ (k - (j : ℕ)) *
          ((k.choose (j : ℕ) : ℕ) : Work.MotV.Om D))
      ∈ asTwFieldAt D (w + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀) := by
    intro k hk
    obtain ⟨c, hc⟩ : ∃ c : RatFunc 𝕜, algebraMap (RatFunc 𝕜) (Work.MotV.Om D) c =
        (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀) ^ (k - (j : ℕ)) *
          ((k.choose (j : ℕ) : ℕ) : Work.MotV.Om D) :=
      ⟨u₀ ^ (k - (j : ℕ)) * ((k.choose (j : ℕ) : ℕ) : RatFunc 𝕜), by
        rw [map_mul, map_pow, map_natCast]⟩
    rw [← hc]
    refine IntermediateField.mul_mem (asTwFieldAt D (w + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀)) ?_
      (IntermediateField.algebraMap_mem (asTwFieldAt D (w + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀)) c)
    rw [interpPoly_coeff D (w + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀)
      ⟨k, Finset.mem_range.mp hk⟩, asTwFieldAt]
    exact IntermediateField.subset_adjoin (RatFunc 𝕜) _ (Set.mem_range_self _)
  exact IntermediateField.sum_mem (asTwFieldAt D (w + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀)) hmem

/-- **Root independence of the AS twist field (shifts by elements of `K`).**  If `u` lies in the
image of `K = RatFunc 𝕜` in `Om D`, then the field generated by the twisted coordinates at the
roots `w` and `w + u` is the same.  In particular, two roots of `X^5 - X - g` differing by an
element of the prime field generate the same twist field (`asTwFieldAt_eq_of_root`). -/
theorem asTwFieldAt_eq_of_mem_range (D : Work.MotV.KleinData 𝕜) (w : Work.MotV.Om D)
    (u : Work.MotV.Om D) (hu : u ∈ Set.range (algebraMap (RatFunc 𝕜) (Work.MotV.Om D))) :
    asTwFieldAt D (w + u) = asTwFieldAt D w := by
  obtain ⟨u₀, rfl⟩ := hu
  refine le_antisymm ?_ (asTwFieldAt_le_of_mem_range D w u₀)
  have h := asTwFieldAt_le_of_mem_range D (w + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀) (-u₀)
  rw [show (w + algebraMap (RatFunc 𝕜) (Work.MotV.Om D) u₀) +
      algebraMap (RatFunc 𝕜) (Work.MotV.Om D) (-u₀) = w by
    rw [map_neg]; ring] at h
  exact h

end
end Work.MotV5
