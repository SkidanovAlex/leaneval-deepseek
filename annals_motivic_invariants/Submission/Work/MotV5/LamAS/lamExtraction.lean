import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

/-!
# The Artin–Schreier LAM extraction

`Work.MotV5.LamAS.lamExtraction` is the field-theoretic core of the **LAM** node of the
characteristic-`5` branch of Lin–Shinder's `theorem_1_2_3`: a Galois-twisted Klein point over a
finite Galois extension `L/K` of `K = 𝕜(t)` whose twisting extension is the Artin–Schreier
extension `K⟮asRoot g⟯ ⊆ L` produces a `K`-rational point of the Klein cone.

## The mathematics

Let `K = RatFunc 𝕜`, `L/K` finite Galois, `W = asRoot g ∈ L` an Artin–Schreier root
(`W⁵ - W = g`), `x : Fin 5 → L` a nonzero Klein point
(`kleinP a b x = 0`), and suppose that the Galois action on `x` is the twist of the shift action
on the Artin–Schreier root:

* `γ W = W + c γ` for all `γ : Gal(L/K)`,
* `γ (x i) = μ γ * x (i + c γ)` for all `γ` and `i`, with `μ γ ≠ 0`.

The conclusion is that some nonzero `y : Fin 5 → K` has its **Artin–Schreier Galois coordinates**
`asCoord (asRoot g) (algebraMap y)` on the Klein cone over `K̄ = Kb 𝕜`.

The proof is a descent argument:

1. *(interpolation)* Lagrange interpolation of `x` at the five distinct nodes `W + i`
   (`i : Fin 5`) produces a polynomial `f ∈ L[X]` of degree `< 5` with
   `f.eval (W + i) = x i`.  The existence and the injectivity of the node map use that the nodes
   `W + i` are pairwise distinct in characteristic `5` (`fin5_cast_injective`).
2. *(semi-invariance)* For `γ : Gal(L/K)` the two polynomials `f.map γ` and `C (μ γ) * f` have
   degree `< 5` and agree at the five points `γ (W + i)` (using the Galois laws above, the shift
   identity `γ (W + i) = W + (i + c γ)` — `fin5_cast_add` — and `hxμ`).  Hence they are equal, and
   comparing coefficients gives `γ (f.coeff j) = μ γ * f.coeff j` for all `j`.
3. *(descent)* Pick `j₀` with `yL j₀ ≠ 0`, where `yL = f.coeff`.  The elements
   `(yL j₀)⁻¹ * yL j` are fixed by the whole Galois group, hence lie in the image of `K` (the
   fundamental theorem of Galois theory, `IsGalois.mem_range_algebraMap_iff_fixed`).  So there is
   `zz : Fin 5 → K` with `algebraMap zz j = (yL j₀)⁻¹ * yL j`.
4. *(conclusion)* `asCoord W (algebraMap zz) = (yL j₀)⁻¹ • x`; the Klein quadrics are homogeneous
   of degree `2`, so evaluating at this point gives `0` on the nose, and pushing along
   `K → Kb` (`kleinP_map'`) gives the statement.

Note the conclusion lives over `Kb 𝕜 = AlgebraicClosure (RatFunc 𝕜)`, so no geometric transport is
needed at the end.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.MotV5.LamAS

open Polynomial

/-! ## Elementary arithmetic in `Fin 5` over a field of characteristic `5` -/

/-- `n` and `n % 5` have the same image in characteristic `5`. -/
theorem natCast_eq_mod_five {F : Type*} [CommSemiring F] [CharP F 5] (n : ℕ) :
    ((n : ℕ) : F) = ((n % 5 : ℕ) : F) := by
  conv_lhs => rw [← Nat.div_add_mod n 5]
  push_cast
  rw [show (5 : F) = 0 by exact CharP.cast_eq_zero F 5]
  first | refl_ring1 | ring

/-- Addition in `Fin 5` is addition of the images in a field of characteristic `5`. -/
theorem fin5_cast_add {F : Type*} [CommSemiring F] [CharP F 5] (i c : Fin 5) :
    (((i + c : Fin 5) : ℕ) : F) = ((i : ℕ) : F) + ((c : ℕ) : F) := by
  rw [Fin.val_add]
  rw [← natCast_eq_mod_five (F := F) (i.val + c.val)]
  push_cast
  first | refl_ring1 | ring

/-- The five residues `0, …, 4` are distinct in a field of characteristic `5`. -/
theorem fin5_cast_injective {F : Type*} [Field F] [CharP F 5] :
    Function.Injective (fun i : Fin 5 => ((i.val : ℕ) : F)) := by
  intro i j hij
  have hsub : (((i.val : ℤ) - (j.val : ℤ) : ℤ) : F) = 0 := by
    push_cast
    simp [hij]
  have hdvd : (5 : ℤ) ∣ (i.val : ℤ) - (j.val : ℤ) :=
    (CharP.intCast_eq_zero_iff F 5 _).mp hsub
  have hi := i.isLt
  have hj := j.isLt
  have h0 : (i.val : ℤ) - (j.val : ℤ) = 0 := by
    obtain ⟨k, hk⟩ := hdvd
    omega
  exact Fin.ext (by omega)

/-- The integral cast of `k : Fin 5` is the residue class of `k.val`. -/
theorem fin5_intCast_eq {F : Type*} [Ring F] [CharP F 5] (k : Fin 5) :
    algebraMap ℤ F ((k : Fin 5) : ℤ) = ((k : ℕ) : F) := by
  norm_num

/-! ## Interpolation at the five nodes `w + i` -/

/-- **Lagrange interpolation at the Artin–Schreier nodes.**  For a field `F` of characteristic `5`,
an element `w : F` and a vector `x : Fin 5 → F` there is a polynomial `f` of degree `< 5` with
`f.eval (w + i) = x i` for all `i : Fin 5`.  (The nodes are pairwise distinct because the residues
`0, …, 4` are.) -/
theorem exists_interp_poly {F : Type*} [Field F] [CharP F 5] (w : F) (x : Fin 5 → F) :
    ∃ f : Polynomial F, f.natDegree < 5 ∧ ∀ i : Fin 5, f.eval (w + ((i : ℕ) : F)) = x i := by
  classical
  set v : Fin 5 → F := fun i => w + ((i : ℕ) : F) with hv
  have hinj : Set.InjOn v (↑(Finset.univ : Finset (Fin 5))) := by
    intro i _ j _ hij
    simp only [hv] at hij
    exact fin5_cast_injective (add_left_cancel hij)
  refine ⟨(Lagrange.interpolate (Finset.univ : Finset (Fin 5)) v) x, ?_, ?_⟩
  · rcases eq_or_ne ((Lagrange.interpolate (Finset.univ : Finset (Fin 5)) v) x) 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]; norm_num
    · rw [Polynomial.natDegree_lt_iff_degree_lt h0]
      simpa using Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin 5))) (v := v) x
        hinj
  · intro i
    exact Lagrange.eval_interpolate_at_node x hinj (Finset.mem_univ i)

/-- A polynomial of degree `< 5` with the five distinct roots `w, w+1, …, w+4` is zero. -/
theorem eq_zero_of_natDegree_lt_five {F : Type*} [Field F] [CharP F 5] (w : F) (p : Polynomial F)
    (hdeg : p.natDegree < 5) (hroot : ∀ i : Fin 5, p.eval (w + ((i : ℕ) : F)) = 0) : p = 0 := by
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero p ?_ hroot ?_
  · intro i j hij
    simp only at hij
    exact fin5_cast_injective (add_left_cancel hij)
  · simpa using hdeg

/-! ## Compatibilities of `asCoord` and of the Klein quadrics with ring homomorphisms -/

/-- `asCoord` commutes with ring homomorphisms. -/
theorem asCoord_map {A B : Type*} [Field A] [Field B] (f : A →+* B)
    (w : A) (y : Fin 5 → A) (i : Fin 5) :
    f (Work.MotV.asCoord w y i) = Work.MotV.asCoord (f w) (fun j => f (y j)) i := by
  simp only [Work.MotV.asCoord, map_sum, map_mul, map_pow, map_add, map_natCast]

/-- `asCoord` is linear in the coefficient vector. -/
theorem asCoord_smul' {F : Type*} [Field F] (w c : F) (y : Fin 5 → F) :
    Work.MotV.asCoord w (fun i => c * y i) = fun i => c * Work.MotV.asCoord w y i := by
  funext i
  simp only [Work.MotV.asCoord]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- The Klein Pfaffians are polynomials with integer coefficients, hence commute with ring
homomorphisms. -/
theorem kleinP_map' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a b : R)
    (x : Fin 5 → R) (j : Fin 5) :
    f (Work.MotK.kleinP a b x j) = Work.MotK.kleinP (f a) (f b) (fun i => f (x i)) j := by
  fin_cases j <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4, map_add, map_sub, map_mul, map_pow,
      map_neg]

/-- The Klein Pfaffians are homogeneous of degree `2`. -/
theorem kleinP_homog' {R : Type*} [CommRing R] (a b : R) (lam : R) (z : Fin 5 → R) :
    Work.MotK.kleinP a b (fun i => lam * z i) = fun k => lam ^ 2 * Work.MotK.kleinP a b z k := by
  funext k
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4] <;>
    first | refl_ring1 | ring

/-! ## The extraction -/

set_option maxHeartbeats 1200000 in
theorem lamExtraction (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜)
    (L : IntermediateField (RatFunc 𝕜) (Work.MotV.Kb 𝕜))
    [IsGalois (RatFunc 𝕜) ↥L] [FiniteDimensional (RatFunc 𝕜) ↥L]
    (hW : Work.MotV5.asRoot g ∈ L)
    (x : Fin 5 → ↥L) (hx0 : x ≠ 0)
    (hx : ∀ k, Work.MotK.kleinP (algebraMap (RatFunc 𝕜) ↥L (algebraMap 𝕜 (RatFunc 𝕜) D.a))
        (algebraMap (RatFunc 𝕜) ↥L (algebraMap 𝕜 (RatFunc 𝕜) D.b)) x k = 0)
    (c : (↥L ≃ₐ[RatFunc 𝕜] ↥L) → Fin 5)
    (hc : ∀ γ, γ ⟨Work.MotV5.asRoot g, hW⟩ = ⟨Work.MotV5.asRoot g, hW⟩
        + algebraMap ℤ ↥L ((c γ : Fin 5) : ℤ))
    (μ : (↥L ≃ₐ[RatFunc 𝕜] ↥L) → ↥L)
    (hμ : ∀ γ, μ γ ≠ 0)
    (hxμ : ∀ (γ : ↥L ≃ₐ[RatFunc 𝕜] ↥L) (i : Fin 5), γ (x i) = μ γ * x (i + c γ)) :
    ∃ y : Fin 5 → RatFunc 𝕜, y ≠ 0 ∧ ∀ k,
      Work.MotK.kleinP (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
        (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
        (Work.MotV.asCoord (Work.MotV5.asRoot g)
          (fun j => algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (y j))) k = 0 := by
  classical
  -- the Artin–Schreier root as an element of `L`
  set W : ↥L := ⟨Work.MotV5.asRoot g, hW⟩ with hWdef
  have hcW : ∀ γ : ↥L ≃ₐ[RatFunc 𝕜] ↥L, γ W = W + algebraMap ℤ ↥L ((c γ : Fin 5) : ℤ) :=
    fun γ => hc γ
  -- interpolation of `x` at the nodes `W + i`
  obtain ⟨f, hfdeg, hfeval⟩ := exists_interp_poly (F := ↥L) W x
  set yL : Fin 5 → ↥L := fun j => f.coeff (j : ℕ) with hyLdef
  have hasCoord : Work.MotV.asCoord W yL = x := by
    funext i
    simp only [Work.MotV.asCoord, hyLdef]
    rw [Fin.sum_univ_eq_sum_range (fun n => f.coeff n * (W + ((i : ℕ) : ↥L)) ^ n) 5,
      ← Polynomial.eval_eq_sum_range' hfdeg (W + ((i : ℕ) : ↥L))]
    exact hfeval i
  -- the coefficients of the interpolation polynomial are semi-invariant
  have hstep' : ∀ (γ : ↥L ≃ₐ[RatFunc 𝕜] ↥L) (j : Fin 5),
      γ (f.coeff (j : ℕ)) = μ γ * f.coeff (j : ℕ) := by
    intro γ j
    have hCD : f.map (γ : ↥L →+* ↥L) = Polynomial.C (μ γ) * f := by
      have hdegD : (f.map (γ : ↥L →+* ↥L) - Polynomial.C (μ γ) * f).natDegree < 5 := by
        calc (f.map (γ : ↥L →+* ↥L) - Polynomial.C (μ γ) * f).natDegree
            ≤ max (f.map (γ : ↥L →+* ↥L)).natDegree (Polynomial.C (μ γ) * f).natDegree :=
              Polynomial.natDegree_sub_le _ _
          _ ≤ f.natDegree := max_le Polynomial.natDegree_map_le (Polynomial.natDegree_C_mul_le _ _)
          _ < 5 := hfdeg
      have hz : f.map (γ : ↥L →+* ↥L) - Polynomial.C (μ γ) * f = 0 := by
        refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
          (p := f.map (γ : ↥L →+* ↥L) - Polynomial.C (μ γ) * f)
          (f := fun i : Fin 5 => γ (W + ((i : ℕ) : ↥L))) ?_ ?_ ?_
        · intro i j hij
          simp only at hij
          exact fin5_cast_injective (add_left_cancel (γ.injective hij))
        · intro i
          have h1 : γ W = W + ((c γ : Fin 5) : ℕ) := by
            rw [hcW γ, fin5_intCast_eq]
          have harg : γ (W + ((i : ℕ) : ↥L)) = W + (((i + c γ : Fin 5) : ℕ) : ↥L) := by
            rw [map_add, h1, map_natCast, fin5_cast_add]
            abel
          have hkey : Polynomial.eval₂ (γ : ↥L →+* ↥L) (γ (W + ((i : ℕ) : ↥L))) f
              = γ (f.eval (W + ((i : ℕ) : ↥L))) :=
            Polynomial.eval₂_hom (γ : ↥L →+* ↥L) (W + ((i : ℕ) : ↥L))
          rw [Polynomial.eval_sub, Polynomial.eval_map, Polynomial.eval_mul, Polynomial.eval_C]
          rw [hkey, hfeval, harg, hfeval, hxμ γ i, sub_self]
        · simpa using hdegD
      exact sub_eq_zero.mp hz
    rw [← Polynomial.coeff_C_mul, ← hCD, Polynomial.coeff_map]
    rfl
  have hstep : ∀ (γ : ↥L ≃ₐ[RatFunc 𝕜] ↥L) (j : Fin 5), γ (yL j) = μ γ * yL j := by
    intro γ j
    rw [hyLdef]
    exact hstep' γ j
  -- a nonzero coefficient, and the invariant normalisation
  have hyLne : yL ≠ 0 := by
    intro h
    apply hx0
    rw [← hasCoord, h]
    funext i
    simp [Work.MotV.asCoord]
  obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hyLne
  simp only [Pi.zero_apply] at hj0
  have hfix : ∀ j : Fin 5, ∃ zz : RatFunc 𝕜,
      algebraMap (RatFunc 𝕜) ↥L zz = (yL j0)⁻¹ * yL j := by
    intro j
    rw [← Set.mem_range, IsGalois.mem_range_algebraMap_iff_fixed]
    intro γ
    rw [map_mul, map_inv₀, hstep γ j0, hstep γ j]
    have hμγ : μ γ ≠ 0 := hμ γ
    field_simp
  choose zz hz using hfix
  refine ⟨zz, ?_, ?_⟩
  · -- `zz` is nonzero
    intro hzz
    have h1 := hz j0
    rw [hzz] at h1
    simp only [Pi.zero_apply, map_zero] at h1
    rw [inv_mul_cancel₀ hj0] at h1
    exact zero_ne_one h1
  · -- the Klein equations over `Kb 𝕜`
    intro k
    rw [show (fun j => algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (zz j))
        = fun j => algebraMap ↥L (Work.MotV.Kb 𝕜) ((yL j0)⁻¹ * yL j) from
          funext (fun j => by
            rw [← hz j,
              IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥L (Work.MotV.Kb 𝕜) (zz j)])]
    have hcoord : Work.MotV.asCoord (Work.MotV5.asRoot g)
          (fun j => algebraMap ↥L (Work.MotV.Kb 𝕜) ((yL j0)⁻¹ * yL j))
        = fun i => algebraMap ↥L (Work.MotV.Kb 𝕜) ((yL j0)⁻¹ * x i) := by
      have h2 : Work.MotV.asCoord (Work.MotV5.asRoot g)
            (fun j => algebraMap ↥L (Work.MotV.Kb 𝕜) (yL j))
          = fun i => algebraMap ↥L (Work.MotV.Kb 𝕜) (x i) := by
        have h3 : Work.MotV.asCoord (algebraMap ↥L (Work.MotV.Kb 𝕜) W)
              (fun j => algebraMap ↥L (Work.MotV.Kb 𝕜) (yL j))
            = fun i => algebraMap ↥L (Work.MotV.Kb 𝕜) (Work.MotV.asCoord W yL i) :=
          funext (fun i => (asCoord_map (algebraMap ↥L (Work.MotV.Kb 𝕜)) W yL i).symm)
        rw [show algebraMap ↥L (Work.MotV.Kb 𝕜) W = Work.MotV5.asRoot g from rfl] at h3
        rw [h3, hasCoord]
      rw [show (fun j => algebraMap ↥L (Work.MotV.Kb 𝕜) ((yL j0)⁻¹ * yL j))
            = (fun j => algebraMap ↥L (Work.MotV.Kb 𝕜) ((yL j0)⁻¹) *
                algebraMap ↥L (Work.MotV.Kb 𝕜) (yL j)) from
              funext (fun j => map_mul _ _ _)]
      rw [asCoord_smul' (w := Work.MotV5.asRoot g)
            (c := algebraMap ↥L (Work.MotV.Kb 𝕜) ((yL j0)⁻¹))
            (y := fun j => algebraMap ↥L (Work.MotV.Kb 𝕜) (yL j)), h2]
      funext i
      rw [map_mul]
    rw [hcoord]
    rw [show algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a
          = algebraMap ↥L (Work.MotV.Kb 𝕜)
              (algebraMap (RatFunc 𝕜) ↥L (algebraMap 𝕜 (RatFunc 𝕜) D.a)) from by
        rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Kb 𝕜) D.a,
            ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥L (Work.MotV.Kb 𝕜)
              (algebraMap 𝕜 (RatFunc 𝕜) D.a)]]
    rw [show algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b
          = algebraMap ↥L (Work.MotV.Kb 𝕜)
              (algebraMap (RatFunc 𝕜) ↥L (algebraMap 𝕜 (RatFunc 𝕜) D.b)) from by
        rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Kb 𝕜) D.b,
            ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥L (Work.MotV.Kb 𝕜)
              (algebraMap 𝕜 (RatFunc 𝕜) D.b)]]
    rw [← kleinP_map' (algebraMap ↥L (Work.MotV.Kb 𝕜))
      (algebraMap (RatFunc 𝕜) ↥L (algebraMap 𝕜 (RatFunc 𝕜) D.a))
      (algebraMap (RatFunc 𝕜) ↥L (algebraMap 𝕜 (RatFunc 𝕜) D.b))
      (fun i => (yL j0)⁻¹ * x i) k]
    rw [kleinP_homog']
    simp only [hx k, mul_zero, map_zero]

end Work.MotV5.LamAS
