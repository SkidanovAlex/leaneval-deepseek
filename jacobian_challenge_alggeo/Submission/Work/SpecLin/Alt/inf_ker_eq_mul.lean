import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SpecLin.Alt

open scoped TensorProduct

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

/-- Auxiliary general statement: if `T` is an `R`-algebra and `f : T →+* R` is a retraction of
the structure map `algebraMap R T` (i.e. `f (algebraMap R T r) = r` for all `r`), then for any
ideal `m` of `R` the kernel of `f` meets the extension `m·T` exactly in the product
`(m·T) * ker f`.

The nontrivial inclusion is `ker f ⊓ m·T ≤ (m·T) * ker f`: for `x = ∑ tᵢ (mᵢ · 1) ∈ m·T` one
has `x - algebraMap R T (f x) = ∑ (tᵢ - algebraMap R T (f tᵢ)) (mᵢ · 1) ∈ ker f * m·T`, and
`f x = 0` when `x ∈ ker f`. -/
private lemma aux_ker_inf_map_eq_mul {R T : Type*} [CommRing R] [CommRing T] [Algebra R T]
    (f : T →+* R) (hf : ∀ r : R, f (algebraMap R T r) = r) (m : Ideal R) :
    RingHom.ker f ⊓ m.map (algebraMap R T) = m.map (algebraMap R T) * RingHom.ker f := by
  -- `f` maps the extension `m·T` into `m`.
  have hJf : m.map (algebraMap R T) ≤ m.comap f := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simpa [hf] using hr
  -- The submodule of elements `x ∈ m·T` whose "error" `x - algebraMap R T (f x)` lies in
  -- `m·T * ker f`.  It contains all generators and hence all of `m·T`.
  let N : Submodule T T :=
    { carrier := {x | x ∈ m.map (algebraMap R T) ∧
        x - algebraMap R T (f x) ∈ m.map (algebraMap R T) * RingHom.ker f}
      add_mem' := by
        intro x y hx hy
        obtain ⟨hxJ, hxN⟩ := hx
        obtain ⟨hyJ, hyN⟩ := hy
        refine ⟨(m.map (algebraMap R T)).add_mem hxJ hyJ, ?_⟩
        rw [f.map_add, map_add]
        have : x + y - (algebraMap R T (f x) + algebraMap R T (f y))
            = (x - algebraMap R T (f x)) + (y - algebraMap R T (f y)) := by ring
        rw [this]
        exact (m.map (algebraMap R T) * RingHom.ker f).add_mem hxN hyN
      zero_mem' := by
        refine ⟨(m.map (algebraMap R T)).zero_mem, ?_⟩
        simp
      smul_mem' := by
        intro c x hx
        obtain ⟨hxJ, hxN⟩ := hx
        refine ⟨(m.map (algebraMap R T)).mul_mem_left c hxJ, ?_⟩
        have hfx : f x ∈ m := hJf hxJ
        have hIterm : c - algebraMap R T (f c) ∈ RingHom.ker f := by
          rw [RingHom.mem_ker, f.map_sub, hf, sub_self]
        have hJterm : algebraMap R T (f x) ∈ m.map (algebraMap R T) :=
          Ideal.mem_map_of_mem (algebraMap R T) hfx
        rw [smul_eq_mul, f.map_mul, map_mul]
        have : c * x - algebraMap R T (f c) * algebraMap R T (f x)
            = c * (x - algebraMap R T (f x)) +
              (c - algebraMap R T (f c)) * algebraMap R T (f x) := by ring
        rw [this]
        refine (m.map (algebraMap R T) * RingHom.ker f).add_mem
          ((m.map (algebraMap R T) * RingHom.ker f).mul_mem_left c hxN) ?_
        have hmem : (c - algebraMap R T (f c)) * algebraMap R T (f x)
            ∈ RingHom.ker f * m.map (algebraMap R T) := Ideal.mul_mem_mul hIterm hJterm
        rwa [Ideal.mul_comm] at hmem }
  have hgen : (algebraMap R T '' (m : Set R)) ⊆ (N : Set T) := by
    rintro _ ⟨r, hr, rfl⟩
    refine ⟨Ideal.mem_map_of_mem (algebraMap R T) hr, ?_⟩
    rw [hf, sub_self]
    exact (m.map (algebraMap R T) * RingHom.ker f).zero_mem
  have hJN : m.map (algebraMap R T) ≤ N := Submodule.span_le.mpr hgen
  apply le_antisymm
  · intro x hx
    rw [Ideal.mem_inf] at hx
    obtain ⟨hxI, hxJ⟩ := hx
    have h2 := (hJN hxJ).2
    rw [RingHom.mem_ker] at hxI
    rw [hxI, map_zero, sub_zero] at h2
    exact h2
  · rw [inf_comm]
    exact Ideal.mul_le_inf

theorem inf_ker_eq_mul {K : Type _} [CommRing K] {A : Type _} [CommRing A] [Algebra K A]
    {R : Type _} [CommRing R] [Algebra K R] (φ : A →ₐ[K] R) (m : Ideal R) :
    RingHom.ker (Algebra.TensorProduct.lift φ (AlgHom.id K R) (fun _ _ => Commute.all _ _)) ⊓
      m.map (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R))
    = m.map (Algebra.TensorProduct.includeRight (R := K) (A := A) (B := R)) *
      RingHom.ker (Algebra.TensorProduct.lift φ (AlgHom.id K R)
        (fun _ _ => Commute.all _ _)) := by
  -- View `A ⊗[K] R` as an `R`-algebra via the right tensor factor.
  letI : Algebra R (A ⊗[K] R) := Algebra.TensorProduct.rightAlgebra (R := K) (A := A) (B := R)
  let f : (A ⊗[K] R) →+* R :=
    (Algebra.TensorProduct.lift φ (AlgHom.id K R) (fun _ _ => Commute.all _ _)).toRingHom
  -- The lift is a retraction of `includeRight`, hence of `algebraMap R (A ⊗[K] R)`.
  have hf : ∀ r : R, f (algebraMap R (A ⊗[K] R) r) = r := by
    intro r
    have h1 := AlgHom.congr_fun
      (Algebra.TensorProduct.lift_comp_includeRight' (R := K) (A := A) (B := R) φ (AlgHom.id K R)
        (fun _ _ => Commute.all _ _)) r
    simpa [f, Algebra.TensorProduct.algebraMap_eq_includeRight] using h1
  have key := aux_ker_inf_map_eq_mul f hf m
  rw [Algebra.TensorProduct.algebraMap_eq_includeRight] at key
  simp only [Ideal.map_coe] at key
  exact key

end Work.SpecLin.Alt
