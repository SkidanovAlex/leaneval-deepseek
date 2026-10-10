import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotC2.aut_functionField
import Submission.Work.MotC5N3.TwistField.asTwistFieldTrue_basic
import Submission.Work.MotT.extend_algEquiv_of_linearDisjoint
import Submission.Work.MotC5N3.Nodes.shiftOf_eq_transAlgEquiv
import Submission.Work.MotC5N3.RigAS.twistFieldTrue_sup_asRoot
import Submission.Work.MotC5N3.LamAS.asPsi
import Submission.Work.MotC5N3.LamAS.asPsi_aux
import Submission.Work.MotC5N3.LamAS.asTransport
import Submission.Work.MotC5N3.LamAS.asIota_range
import Submission.Work.MotC5N3.LamAS.asML_c2
import Submission.Work.MotC5N3.LamAS.asSigmaLift_eq_trans
import Submission.Work.MotC5N3.LamAS.asSigmaLift_comm
import Submission.Work.MotC5N3.LamAS.asF_transfer
import Submission.Work.MotC5N3.LamAS.asF_linearDisjoint
import Submission.Work.MotC5N3.LamAS.asExtendTheta
import Submission.Work.MotC5N3.LamAS.asL2_isGalois
import Submission.Work.MotC5N3.LamAS.asExtension
import Submission.Work.MotC5N3.LamAS.asCompare
import Submission.Work.MotC5N3.LamAS.root_eq_asRoot_add
import Submission.Work.MotC5N3.LamAS.CoordNe.asTwistPoint_coords_ne
import Submission.Work.MotC5N3.LamAS.FixPsi.asPsi_fixes_asF
import Submission.Work.MotC5N3.LamAS.asDefect
import Submission.Work.MotC5N3.GenAux_sigmaS_pow_five_kleinField
import Submission.Work.MotC5N3.TwistField.kleinField_eq_adjoin_genXY
import Submission.Work.MotC2.FuncExt
import Submission.Work.MotC5N3.LamAS.lamAuxB

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000

namespace Work.MotC5N3
open WeierstrassCurve WeierstrassCurve.Affine
open Work.MotC5N3.LamAS
open Work.MotC5N3.LamAS.CoordNe
open Work.MotC5N3.LamAS.FixPsi

/-! ## Auxiliary lemmas: the trivial Artin–Schreier class

Two inputs for the branch of `lam_AS` in which the twisting class is trivial (equivalently
`asRoot g ∈ K`):

* the Klein cone has the **explicit point** `(0, 1, b/a, -b/a, -1)` — a polynomial identity;
* in characteristic `5` the "Galois coordinate" map `y ↦ asCoord w y` is an **interpolation map**
  at the five distinct nodes `w, w+1, …, w+4`, hence (for `w ∈ K`) it is surjective over `K`.

Together they yield the conclusion of `lam_AS`, with `ε = 1`, whenever `asRoot g ∈ K` — i.e. for
the degenerate twisting class `g ∈ ℘(K)`. -/

/-- **The Klein cone has an explicit nonzero point.**  `(0, 1, b/a, -b/a, -1)` lies on all five
Klein Pfaffians for any `a ≠ 0` (the identities are polynomial in `a, b`).  Note `a ≠ 0` and
`b ≠ 0` hold for the Klein data of this branch (`KleinData.Good.ab_ne`). -/
theorem kleinP_explicit_point {𝕜 : Type} [Field 𝕜] (a b : 𝕜) (ha : a ≠ 0) :
    ∀ k : Fin 5, Work.MotK.kleinP a b ![0, 1, b / a, -(b / a), -1] k = 0 := by
  intro k
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val] <;>
    field_simp <;> ring

/-- The Klein Pfaffians are compatible with ring homomorphisms (they are polynomials with integer
coefficients). -/
theorem kleinP_map {𝕜 L : Type} [Field 𝕜] [Field L] (f : 𝕜 →+* L) (a b : 𝕜) (x : Fin 5 → 𝕜)
    (k : Fin 5) :
    Work.MotK.kleinP (f a) (f b) (fun i => f (x i)) k = f (Work.MotK.kleinP a b x k) := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4] <;>
    simp only [map_sub, map_mul, map_pow, map_neg, map_add]

/-- **The Galois-coordinate map is an interpolation map.**  In characteristic `5` the five nodes
`w, w+1, …, w+4` are pairwise distinct, so for every `x : Fin 5 → L` there is `y : Fin 5 → L` with
`asCoord w y = x` (the coefficients of the Lagrange interpolation polynomial of `x` at those
nodes).  Applied with `w ∈ K = K` and `x` a constant vector, it produces `y : Fin 5 → K`. -/
theorem exists_asCoord_eq {L : Type} [Field L] [CharP L 5] (w : L) (x : Fin 5 → L) :
    ∃ y : Fin 5 → L, Work.MotV.asCoord w y = x := by
  classical
  have hchar : ∀ i j : Fin 5, ((i : ℕ) : L) = ((j : ℕ) : L) → i = j := by
    have key : ∀ m n : ℕ, m < 5 → n < 5 → ((m : ℕ) : L) = ((n : ℕ) : L) → m = n := by
      intro m n hm hn h
      rcases le_total m n with hle | hle
      · have h0 : (((n - m : ℕ)) : L) = 0 := by rw [Nat.cast_sub hle, h, sub_self]
        have hdvd : 5 ∣ (n - m) := (CharP.cast_eq_zero_iff L 5 (n - m)).mp h0
        have hlt : n - m < 5 := lt_of_le_of_lt (Nat.sub_le n m) hn
        interval_cases hnm : (n - m) <;> omega
      · have h0 : (((m - n : ℕ)) : L) = 0 := by rw [Nat.cast_sub hle, ← h, sub_self]
        have hdvd : 5 ∣ (m - n) := (CharP.cast_eq_zero_iff L 5 (m - n)).mp h0
        have hlt : m - n < 5 := lt_of_le_of_lt (Nat.sub_le m n) hm
        interval_cases hmn : (m - n) <;> omega
    intro i j hij
    exact Fin.ext (key (i : ℕ) (j : ℕ) i.isLt j.isLt hij)
  set v : Fin 5 → L := fun i => w + (i : L) with hv
  have hinj : Set.InjOn v (↑(Finset.univ : Finset (Fin 5))) := by
    intro i _ j _ hij
    exact hchar i j (add_left_cancel hij)
  set f : Polynomial L := (Lagrange.interpolate (Finset.univ : Finset (Fin 5)) v) x with hf
  have hdeg : f.natDegree < 5 := by
    rcases eq_or_ne f 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]; norm_num
    · rw [Polynomial.natDegree_lt_iff_degree_lt h0, hf]
      simpa using Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset (Fin 5))) (v := v) x
        hinj
  refine ⟨fun j => f.coeff (j : ℕ), ?_⟩
  funext i
  rw [Work.MotV.asCoord]
  have heval : f.eval (w + (i : L)) = x i := by
    rw [hf]
    exact Lagrange.eval_interpolate_at_node x hinj (Finset.mem_univ i)
  have hsum : f.eval (w + (i : L)) = ∑ n ∈ Finset.range 5, f.coeff n * (w + (i : L)) ^ n :=
    Polynomial.eval_eq_sum_range' hdeg (w + (i : L))
  rw [hsum, ← Fin.sum_univ_eq_sum_range (fun n => f.coeff n * (w + (i : L)) ^ n) 5] at heval
  simpa using heval

/-- **The degenerate twisting class.**  If `asRoot g ∈ K` — i.e. `g` is an Artin–Schreier value
`c ^ 5 - c` — then the conclusion of `lam_AS` holds for the parameter `g` (with `ε = 1`): there is a
nonzero `y : Fin 5 → K` whose Galois coordinates `asCoord (asRoot g) y` lie on the Klein
cone.

Proof: push the explicit point `(0, 1, b/a, -b/a, -1)` of `kleinP_explicit_point` into `K`, and
interpolate it at the nodes `W, W+1, …, W+4` (`exists_asCoord_eq`). -/
theorem exists_y_of_asRoot_mem (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K] [Algebra 𝕜 K] [CharP K 5] (D : Work.MotV.KleinData 𝕜)
    (ha : D.a ≠ 0) (hb : D.b ≠ 0) (g : K) (W : K)
    (hW : algebraMap (K) (Work.MotC5N3.KbA K) W = Work.MotC5N3.asRoot g) :
    ∃ y : Fin 5 → K, y ≠ 0 ∧
      ∀ k, Work.MotK.kleinP (algebraMap 𝕜 (Work.MotC5N3.KbA K) D.a)
        (algebraMap 𝕜 (Work.MotC5N3.KbA K) D.b)
        (Work.MotV.asCoord (Work.MotC5N3.asRoot g)
          (fun j => algebraMap (K) (Work.MotC5N3.KbA K) (y j))) k = 0 := by
  classical
  haveI : CharP (K) 5 :=
    charP_of_injective_algebraMap (algebraMap 𝕜 (K)).injective 5
  set x : Fin 5 → K :=
    fun i => algebraMap 𝕜 (K) (![0, 1, D.b / D.a, -(D.b / D.a), -1] i) with hxdef
  have hx1 : x 1 = 1 := by
    show algebraMap 𝕜 (K) (![0, 1, D.b / D.a, -(D.b / D.a), -1] 1) = 1
    norm_num
  have hx : ∀ k, Work.MotK.kleinP (algebraMap 𝕜 (K) D.a)
      (algebraMap 𝕜 (K) D.b) x k = 0 := by
    intro k
    have h0 := kleinP_explicit_point D.a D.b ha k
    have h1 := kleinP_map (algebraMap 𝕜 (K)) D.a D.b
      ![0, 1, D.b / D.a, -(D.b / D.a), -1] k
    rw [h0, map_zero] at h1
    simpa [hxdef] using h1
  have hxne : x ≠ 0 := by
    intro h
    have h1 := congrFun h 1
    rw [hx1] at h1
    exact one_ne_zero (α := K) (by simpa using h1)
  obtain ⟨y, hy⟩ := exists_asCoord_eq W x
  have hyne : y ≠ 0 := by
    intro h0
    have h1 : Work.MotV.asCoord W y = 0 := by
      rw [h0]
      funext i
      rw [Work.MotV.asCoord]
      simp
    rw [hy] at h1
    exact hxne h1
  refine ⟨y, hyne, ?_⟩
  have hcoe : ∀ i, Work.MotV.asCoord (Work.MotC5N3.asRoot g)
      (fun j => algebraMap (K) (Work.MotC5N3.KbA K) (y j)) i
      = algebraMap (K) (Work.MotC5N3.KbA K) (x i) := by
    intro i
    rw [← hW, ← hy]
    simp only [Work.MotV.asCoord, map_sum, map_mul, map_pow, map_add, map_natCast]
  intro k
  have hfun : Work.MotV.asCoord (Work.MotC5N3.asRoot g)
      (fun j => algebraMap (K) (Work.MotC5N3.KbA K) (y j))
      = fun i => algebraMap (K) (Work.MotC5N3.KbA K) (x i) := funext hcoe
  rw [hfun]
  rw [IsScalarTower.algebraMap_apply 𝕜 (K) (Work.MotC5N3.KbA K) D.a,
      IsScalarTower.algebraMap_apply 𝕜 (K) (Work.MotC5N3.KbA K) D.b]
  rw [kleinP_map (algebraMap (K) (Work.MotC5N3.KbA K)) (algebraMap 𝕜 (K) D.a)
    (algebraMap 𝕜 (K) D.b) x k, hx k, map_zero]

/-! ## The two-root model `M = K(W₁,W₂)(E)`

Both twist fields of `lam_AS` live in the compositum `M = K(W₁,W₂)(E) ⊆ Work.MotC5N3.OmA K D`, the function field
of the Klein curve over the compositum `L = K(W₁,W₂)` of the two Artin–Schreier fields.  This is
where the isomorphism `θ` extends (`Work.MotT.extend_algEquiv_of_linearDisjoint`: both `Fᵢ` are
linearly disjoint from `L` over `K` — their constants in `Work.MotC5N3.KbA K` are `K`, by
`asTwistFieldTrue_constants` — and `Fᵢ ⊔ L = M`) and where the classification
`Work.MotC2.aut_functionField` applies. -/

variable {𝕜 : Type} [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K]

noncomputable section

/-- The image of `L = K(W₁, W₂)` in `Work.MotC5N3.OmA K D`. -/
def asK2D (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    IntermediateField (K) (Work.MotC5N3.OmA K D) :=
  IntermediateField.adjoin (K)
    ({algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot f₁),
      algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot f₂)} :
        Set (Work.MotC5N3.OmA K D))

/-- The model `M = K(W₁,W₂)(E) ⊆ Work.MotC5N3.OmA K D`. -/
def asM2 (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    IntermediateField (K) (Work.MotC5N3.OmA K D) :=
  Work.MotC5N3.kleinField K D ⊔ asK2D D f₁ f₂

theorem asRoot_mem_asK2D_left (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot f₁) ∈ asK2D D f₁ f₂ :=
  IntermediateField.subset_adjoin _ _ (by simp)

theorem asRoot_mem_asK2D_right (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot f₂) ∈ asK2D D f₁ f₂ :=
  IntermediateField.subset_adjoin _ _ (by simp)

theorem asK2D_le_asM2 (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    asK2D D f₁ f₂ ≤ asM2 D f₁ f₂ := le_sup_right

theorem kleinField_le_asM2 (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    Work.MotC5N3.kleinField K D ≤ asM2 D f₁ f₂ := le_sup_left

theorem asK2D_comm (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    asK2D D f₁ f₂ = asK2D D f₂ f₁ := by
  rw [asK2D, asK2D, Set.pair_comm]

theorem asM2_comm (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    asM2 D f₁ f₂ = asM2 D f₂ f₁ := by
  rw [asM2, asM2, asK2D_comm]

theorem asFieldL_le_asM2 (D : Work.MotV.KleinData 𝕜) (f₁ f₂ : K) :
    Work.MotC5N3.asFieldL D f₁ ≤ asM2 D f₁ f₂ := by
  rw [asM2, Work.MotC5N3.asFieldL]
  refine sup_le le_sup_left (le_trans ?_ le_sup_right)
  rw [asK2D]
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact IntermediateField.subset_adjoin _ _ (by simp)

theorem asTwistFieldTrue_le_asM2 (D : Work.MotV.KleinData 𝕜) (g : K)
    (τ : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    {f₁ f₂ : K} (hg : g = f₁ ∨ g = f₂) :
    Work.MotC5N3.asTwistFieldTrue D g τ σS ≤ asM2 D f₁ f₂ := by
  rcases hg with hg | hg
  · rw [hg]
    exact le_trans (Work.MotC5N3.asTwistFieldTrue_le_asFieldL D f₁ τ σS) (asFieldL_le_asM2 D f₁ f₂)
  · rw [hg]
    exact le_trans (Work.MotC5N3.asTwistFieldTrue_le_asFieldL D f₂ τ σS)
      ((asFieldL_le_asM2 D f₂ f₁).trans (le_of_eq (asM2_comm D f₁ f₂).symm))

end

end Work.MotC5N3
