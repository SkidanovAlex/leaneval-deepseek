import Mathlib
import Submission.Work.Modular.Poisson.Std

/-!
# The dual lattice of `L` in terms of the lattice isomorphism `d : L ≅ ℤⁿ`

If `d : ℝⁿ ≃ₗ[ℝ] ℝⁿ` maps a lattice `L` onto the standard integer lattice `ℤⁿ`
(`hd : x ∈ L ↔ d x ∈ ℤⁿ`), then the dual lattice `L* = {y | ∀ x ∈ L, ⟪y, x⟫ ∈ ℤ}`
is the image of `ℤⁿ` under the (Euclidean) adjoint of `d`:

  `L* = (adjoint d) '' ℤⁿ = { adjoint d (intVecE k) | k : Fin n → ℤ }`.

The proof rests on three elementary facts, proved below:

* the adjoint identity `⟪adjoint d w, x⟫ = ⟪w, d x⟫`;
* `intLatticeE` is self-dual (`inner_mem_intLatticeE`);
* the standard basis vectors `intVecE (Pi.single i 1)` are the coordinate functionals
  (`inner_intVecE_single`).
-/

namespace Work.Poisson

open Work.Modular

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The integer vector attached to `k : ι → ℤ` lies in the integer lattice `ℤ^ι`. -/
lemma intVecE_mem_intLatticeE (k : ι → ℤ) : intVecE k ∈ intLatticeE ι := by
  rw [mem_intLatticeE]
  intro i
  exact ⟨k i, rfl⟩

/-- The inner product of two vectors of the integer lattice `ℤ^ι` is an integer. -/
lemma inner_mem_intLatticeE {x y : EuclideanSpace ℝ ι}
    (hx : x ∈ intLatticeE ι) (hy : y ∈ intLatticeE ι) :
    ∃ m : ℤ, inner ℝ x y = (m : ℝ) := by
  rw [mem_intLatticeE] at hx hy
  choose mx hmx using hx
  choose my hmy using hy
  refine ⟨∑ i, mx i * my i, ?_⟩
  rw [PiLp.inner_apply]
  simp only [hmx, hmy, Real.inner_apply]
  push_cast
  ring

/-- Testing against the standard basis vector `e i` reads off the `i`-th coordinate. -/
lemma inner_intVecE_single (w : EuclideanSpace ℝ ι) (i : ι) :
    inner ℝ w (intVecE (Pi.single i (1 : ℤ) : ι → ℤ)) = w i := by
  rw [PiLp.inner_apply]
  simp only [intVecE, intVec, WithLp.ofLp_toLp, Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; simp at h

/-- If a linear isomorphism `d` carries the lattice `L` onto `ℤⁿ`, then the dual lattice of `L`
is the image of `ℤⁿ` under the adjoint of `d`. -/
theorem dualLattice_eq_T {n : ℕ}
    (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    (hspan : Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin n))) = ⊤)
    (d : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n))
    (hd : ∀ x : EuclideanSpace ℝ (Fin n), x ∈ L ↔ d x ∈ Work.Modular.intLatticeE (Fin n))
    (y : EuclideanSpace ℝ (Fin n)) :
    y ∈ Work.Modular.dualLattice L ↔ ∃ k : Fin n → ℤ,
      y = LinearMap.adjoint d.toLinearMap (Work.Modular.intVecE k) := by
  constructor
  · -- `y` is in the dual: send it back through `adjoint d.symm` and read off coordinates.
    intro hy
    set w : EuclideanSpace ℝ (Fin n) :=
      LinearMap.adjoint d.symm.toLinearMap y with hw
    have hyw : y = LinearMap.adjoint d.toLinearMap w := by
      refine (ext_inner_right ℝ (x := LinearMap.adjoint d.toLinearMap w) (y := y) ?_).symm
      intro v
      rw [LinearMap.adjoint_inner_left, hw, LinearMap.adjoint_inner_left]
      simp
    have hwmem : w ∈ Work.Modular.intLatticeE (Fin n) := by
      rw [Work.Modular.mem_intLatticeE]
      intro i
      set e : EuclideanSpace ℝ (Fin n) :=
        Work.Modular.intVecE (Pi.single i (1 : ℤ) : Fin n → ℤ) with he
      have heint : e ∈ Work.Modular.intLatticeE (Fin n) := by
        rw [he]; exact intVecE_mem_intLatticeE _
      have hxL : d.symm e ∈ L := (hd (d.symm e)).mpr (by simpa using heint)
      obtain ⟨m, hm⟩ := hy (d.symm e) hxL
      refine ⟨m, ?_⟩
      have h1 : inner ℝ w e = inner ℝ y (d.symm e) := by
        rw [hw]; exact LinearMap.adjoint_inner_left d.symm.toLinearMap e y
      have h2 : inner ℝ w e = w i := by rw [he]; exact inner_intVecE_single w i
      rw [← h2, h1, hm]
    obtain ⟨k, hk⟩ : ∃ k : Fin n → ℤ, w = Work.Modular.intVecE k := by
      rw [Work.Modular.mem_intLatticeE] at hwmem
      choose k hk using hwmem
      exact ⟨k, by ext i; rw [Work.Modular.intVecE_apply]; exact hk i⟩
    exact ⟨k, by rw [hyw, hk]⟩
  · -- Conversely, `adjoint d (intVecE k)` pairs integrally with every element of `L`.
    rintro ⟨k, rfl⟩ x hx
    have hdx : d x ∈ Work.Modular.intLatticeE (Fin n) := (hd x).mp hx
    have hk : Work.Modular.intVecE k ∈ Work.Modular.intLatticeE (Fin n) :=
      intVecE_mem_intLatticeE k
    obtain ⟨m, hm⟩ := inner_mem_intLatticeE hk hdx
    refine ⟨m, ?_⟩
    rw [LinearMap.adjoint_inner_left]
    exact hm

end Work.Poisson
