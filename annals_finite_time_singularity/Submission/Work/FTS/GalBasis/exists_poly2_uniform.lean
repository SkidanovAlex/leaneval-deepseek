import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Submission.Work.FTS.GalBasis.PolySumDefs
import Submission.Work.FTS.GalBasis.isPolySum_add
import Submission.Work.FTS.GalBasis.isPolySum_mul
import Submission.Work.FTS.GalBasis.exists_fin_monomial_sum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Uniform approximation of a continuous function on a rectangle by two-variable polynomials

We prove that every function `h : ℝ → ℝ → ℝ` which is continuous on a rectangle
`[A,B] × [C,D]` can be uniformly approximated there by a finite sum of two-variable monomials
`c * z ^ p * θ ^ q`, with `p q : ℕ` and `c : ℝ`.

The argument is the Stone–Weierstrass theorem.  Writing `s` for the rectangle, the monomial
sums (`Work.FTS.GalBasis.IsPolySum`) form a subalgebra `polySumSubalgebra s` of `C(s, ℝ)`
which contains the two coordinate projections and hence separates points; therefore it is
dense, and `exists_mem_subalgebra_near_continuousMap_of_separatesPoints` provides, for every
`ε > 0`, a monomial sum within `ε` of `h`.  Finally the `Fintype`-indexed sum is reshaped into
a `Fin m`-indexed one (`exists_fin_monomial_sum`), which is the form required.
-/

namespace Work.FTS.GalBasis

open scoped BigOperators

variable (s : Set (ℝ × ℝ))

theorem polySum_zero : IsPolySum (0 : C(s, ℝ)) := by
  refine ⟨Fin 1, inferInstance, fun _ => 0, fun _ => 0, fun _ => 0, ?_⟩
  intro x
  simp

theorem polySum_one : IsPolySum (1 : C(s, ℝ)) := by
  refine ⟨Fin 1, inferInstance, fun _ => 0, fun _ => 0, fun _ => 1, ?_⟩
  intro x
  simp

theorem polySum_algebraMap (r : ℝ) : IsPolySum (algebraMap ℝ C(s, ℝ) r) := by
  refine ⟨Fin 1, inferInstance, fun _ => 0, fun _ => 0, fun _ => r, ?_⟩
  intro x
  simp

/-- The first coordinate projection as a continuous function on `s`. -/
def polySumFst : C(s, ℝ) := ⟨fun x => x.1.1, continuous_subtype_val.fst⟩

/-- The second coordinate projection as a continuous function on `s`. -/
def polySumSnd : C(s, ℝ) := ⟨fun x => x.1.2, continuous_subtype_val.snd⟩

theorem polySumFst_mem : IsPolySum (polySumFst s) := by
  refine ⟨Fin 1, inferInstance, fun _ => 1, fun _ => 0, fun _ => 1, ?_⟩
  intro x
  simp [polySumFst]

theorem polySumSnd_mem : IsPolySum (polySumSnd s) := by
  refine ⟨Fin 1, inferInstance, fun _ => 0, fun _ => 1, fun _ => 1, ?_⟩
  intro x
  simp [polySumSnd]

/-- The subalgebra of `C(s, ℝ)` consisting of the finite sums of two-variable monomials. -/
def polySumSubalgebra : Subalgebra ℝ C(s, ℝ) where
  carrier := {g | IsPolySum g}
  mul_mem' := fun ha hb => isPolySum_mul ha hb
  one_mem' := polySum_one s
  add_mem' := fun ha hb => isPolySum_add ha hb
  zero_mem' := polySum_zero s
  algebraMap_mem' := fun r => polySum_algebraMap s r

/-- The monomial sums separate points: the two coordinate projections already do. -/
theorem polySumSubalgebra_separatesPoints : (polySumSubalgebra s).SeparatesPoints := by
  intro x y hxy
  by_cases h : x.1.1 = y.1.1
  · refine ⟨fun x : s => x.1.2, ⟨polySumSnd s, ?_, rfl⟩, ?_⟩
    · show IsPolySum (polySumSnd s); exact polySumSnd_mem s
    · intro hc
      exact hxy (Subtype.ext (Prod.ext h hc))
  · refine ⟨fun x : s => x.1.1, ⟨polySumFst s, ?_, rfl⟩, h⟩
    · show IsPolySum (polySumFst s); exact polySumFst_mem s

theorem exists_poly2_uniform {h : ℝ → ℝ → ℝ} {A B C D : ℝ} (hAB : A ≤ B) (hCD : C ≤ D)
    (hh : ContinuousOn (Function.uncurry h) (Set.Icc A B ×ˢ Set.Icc C D)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (p q : Fin m → ℕ) (c : Fin m → ℝ),
      ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Icc C D,
        |(∑ k, c k * z ^ (p k) * θ ^ (q k)) - h z θ| < ε := by
  classical
  set s : Set (ℝ × ℝ) := Set.Icc A B ×ˢ Set.Icc C D with hs
  have hcomp : IsCompact s := by
    rw [hs]
    exact isCompact_Icc.prod isCompact_Icc
  haveI : CompactSpace s := isCompact_iff_compactSpace.mp hcomp
  let f : C(s, ℝ) := ⟨s.domRestrict (Function.uncurry h), hh.domRestrict⟩
  obtain ⟨g, hg⟩ := ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    (polySumSubalgebra s) (polySumSubalgebra_separatesPoints s) f ε hε
  have hgB : IsPolySum ((g : polySumSubalgebra s) : C(s, ℝ)) := g.2
  obtain ⟨ι, hι, a, b, c, hc⟩ := hgB
  letI : Fintype ι := hι
  obtain ⟨m, p, q, c', hc'⟩ := exists_fin_monomial_sum a b c
  refine ⟨m, p, q, c', ?_⟩
  intro z hz θ hθ
  have hx : (z, θ) ∈ s := by rw [hs]; exact ⟨hz, hθ⟩
  let x₀ : s := ⟨(z, θ), hx⟩
  have hkey : (∑ k, c' k * z ^ (p k) * θ ^ (q k))
      = ((g : polySumSubalgebra s) : C(s, ℝ)) x₀ := by
    rw [hc' z θ, ← hc x₀]
  have hf : f x₀ = h z θ := rfl
  calc |(∑ k, c' k * z ^ (p k) * θ ^ (q k)) - h z θ|
      = |((g : polySumSubalgebra s) : C(s, ℝ)) x₀ - f x₀| := by rw [hkey, hf]
    _ ≤ ‖((g : polySumSubalgebra s) : C(s, ℝ)) - f‖ := by
        simpa using ContinuousMap.norm_coe_le_norm
          (((g : polySumSubalgebra s) : C(s, ℝ)) - f) x₀
    _ < ε := hg

end Work.FTS.GalBasis
