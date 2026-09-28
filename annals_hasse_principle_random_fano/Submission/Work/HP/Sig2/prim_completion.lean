import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.prim_bezout
import Submission.Work.HP.LatRecurse.ker_finrank

/-!
# Completion of a primitive vector to a `ℤ`-basis (`Sig2.prim_completion`)

For `R ≥ 1` and a primitive `u : Fin R → ℤ` (`Work.HP.IsPrim u`, i.e. the coordinates of `u`
have gcd `1`) there are `R - 1` further integral vectors `v` such that

* `(c₁, c) ↦ c₁ • u + ∑ i, c i • v i` is a bijection `ℤ × ℤ^{R-1} → ℤ^R` (i.e. `u` together
  with the `v i` is a `ℤ`-basis of `ℤ^R`), and
* the realifications of `u` and the `v i` are `ℝ`-linearly independent.

Route: `Work.HP.Lat.prim_bezout u hu` provides `g : Fin R → ℤ` with `∑ i, g i * u i = 1`; define
`f z = ∑ i, g i * z i`, so `f u = 1` and `f` is surjective.  Then `ℤ^R → ℤ × ker f`,
`z ↦ (f z, z - f z • u)`, is a `ℤ`-linear isomorphism, and by `Work.HP.LatRecurse.ker_finrank`
the kernel has rank `R - 1`.  A basis `b` of `ker f` (extracted via `Module.finBasisOfFinrankEq`)
gives the `v i = b i`; it is a basis of `ker f` and the splitting identifies the coordinate map with
an isomorphism.  The realified independence is `linearIndependent_algebraMap_comp_iff` for the
kernel basis together with the real functional `fR` killing the `v i` and sending `u` to `1`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.HP.Sig2

theorem prim_completion {R : ℕ} (hR : 1 ≤ R) (u : Fin R → ℤ) (hu : Work.HP.IsPrim u) :
    ∃ v : Fin (R - 1) → (Fin R → ℤ),
      Function.Bijective (fun c : ℤ × (Fin (R - 1) → ℤ) =>
        c.1 • u + ∑ i, c.2 i • v i) ∧
      (∀ c : ℝ × (Fin (R - 1) → ℝ),
        c.1 • (fun j => (u j : ℝ)) + ∑ i, c.2 i • (fun j => (v i j : ℝ)) = 0 → c = 0) := by
  classical
  obtain ⟨co, hco⟩ := Work.HP.Lat.prim_bezout u hu
  -- The integer linear functional `f z = ∑ i, co i * z i`, with `f u = 1`, hence surjective.
  let f : (Fin R → ℤ) →ₗ[ℤ] ℤ := ∑ i, co i • LinearMap.proj i
  have hf_apply : ∀ z : Fin R → ℤ, f z = ∑ i, co i * z i := by
    intro z; simp [f]
  have hfu : f u = 1 := by rw [hf_apply]; exact hco
  have hf_surj : Function.Surjective f := by
    intro n
    exact ⟨n • u, by rw [map_smul, hfu, smul_eq_mul, mul_one]⟩
  -- The kernel of `f` is free of rank `R - 1`.
  let K := LinearMap.ker f
  have hfin : Module.finrank ℤ K = R - 1 := by
    change Module.finrank ℤ (LinearMap.ker f) = R - 1
    have := Work.HP.LatRecurse.ker_finrank f hf_surj
    omega
  let b : Module.Basis (Fin (R - 1)) ℤ K := Module.finBasisOfFinrankEq ℤ K hfin
  let v : Fin (R - 1) → (Fin R → ℤ) := fun i => (b i : Fin R → ℤ)
  have hf_v : ∀ i, f (v i) = 0 := fun i => (b i : K).2
  have hv_li : LinearIndependent ℤ v := by
    have h := (b.linearIndependent).map' (Submodule.subtype K) (Submodule.ker_subtype K)
    simpa [v, Function.comp_def] using h
  have hsum_repr : ∀ y : K, ∑ i, (b.repr y) i • v i = (y : Fin R → ℤ) := by
    intro y
    have h : (Submodule.subtype K) (∑ i, (b.repr y) i • b i) = (Submodule.subtype K) y := by
      rw [b.sum_repr y]
    rw [map_sum] at h
    simp only [map_smul] at h
    simpa [v] using h
  -- The projection onto the kernel along `u`.
  let wK : (Fin R → ℤ) → K := fun z => ⟨z - f z • u, by
    rw [LinearMap.mem_ker, map_sub, map_smul, hfu, smul_eq_mul, mul_one, sub_self]⟩
  have hfw : ∀ z, (wK z : Fin R → ℤ) = z - f z • u := fun z => rfl
  refine ⟨v, ⟨?_, ?_⟩, ?_⟩
  · -- injectivity of the coordinate map
    rintro ⟨a, g⟩ ⟨a', g'⟩ hxy
    have hfz : ∀ (a : ℤ) (g : Fin (R - 1) → ℤ), f (a • u + ∑ i, g i • v i) = a := by
      intro a g
      have h1 : f (a • u) = a := by rw [map_smul, hfu]; simp
      have h2 : f (∑ i, g i • v i) = 0 := by
        rw [map_sum]
        exact Finset.sum_eq_zero (fun i _ => by rw [map_smul, hf_v i, smul_zero])
      rw [map_add, h1, h2, add_zero]
    have ha : a = a' := by
      have h1 := congrArg f hxy
      rwa [hfz a g, hfz a' g'] at h1
    have hg : g = g' := by
      have hsums : ∑ i, g i • v i = ∑ i, g' i • v i := by
        have h := hxy
        rw [ha] at h
        exact add_left_cancel h
      exact hv_li.fintypeLinearCombination_injective
        (by simpa [Fintype.linearCombination_apply] using hsums)
    exact Prod.ext ha hg
  · -- surjectivity of the coordinate map
    rintro z
    refine ⟨(f z, fun i => b.repr (wK z) i), ?_⟩
    change f z • u + ∑ i, (b.repr (wK z)) i • v i = z
    rw [hsum_repr (wK z), hfw z]
    simp
  · -- realified linear independence
    have hvRli : LinearIndependent ℝ
        (fun i : Fin (R - 1) => fun k : Fin R => ((v i) k : ℝ)) := by
      have h := (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℝ) (v := v)).mpr hv_li
      have heq : (fun i : Fin (R - 1) => fun k : Fin R => ((v i) k : ℝ))
          = (fun i => ⇑(algebraMap ℤ ℝ) ∘ v i) := by
        funext i k
        simp
      rw [heq]
      exact h
    let fR : (Fin R → ℝ) →ₗ[ℝ] ℝ := ∑ i, (co i : ℝ) • LinearMap.proj i
    have hfR_apply : ∀ z : Fin R → ℝ, fR z = ∑ i, (co i : ℝ) * z i := by
      intro z; simp [fR]
    have hfR_u : fR (fun j => (u j : ℝ)) = 1 := by
      rw [hfR_apply]
      have h : ((∑ i, co i * u i : ℤ) : ℝ) = 1 := by rw [hco]; simp
      rw [Int.cast_sum] at h
      simpa [Int.cast_mul] using h
    have hfR_v : ∀ i, fR (fun k => ((v i) k : ℝ)) = 0 := by
      intro i
      rw [hfR_apply]
      have h0 : ∑ k, co k * (v i) k = 0 := by rw [← hf_apply]; exact hf_v i
      have h : ((∑ k, co k * (v i) k : ℤ) : ℝ) = 0 := by rw [h0]; simp
      rw [Int.cast_sum] at h
      simpa [Int.cast_mul] using h
    intro c hc
    have h1 : c.1 = 0 := by
      have h := congrArg fR hc
      simp only [map_add, map_smul, map_sum, map_zero, hfR_u, hfR_v, smul_eq_mul, mul_one,
        mul_zero, Finset.sum_const_zero, add_zero] at h
      exact h
    have h2 : c.2 = 0 := by
      have hsum : ∑ i, c.2 i • (fun k => ((v i) k : ℝ)) = 0 := by
        have h := hc
        rw [h1] at h
        simpa using h
      funext i
      exact (Fintype.linearIndependent_iff.mp hvRli) c.2 hsum i
    exact Prod.ext h1 h2

end Work.HP.Sig2
