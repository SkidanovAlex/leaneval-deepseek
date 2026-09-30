import Mathlib
import Submission.Work.BW.sieg2_lattice_defs
import Submission.Work.BW.sieg2KernelDefs
import Submission.Work.BW.sieg2_PhiE_aux
import Submission.Work.BW.exists_int_mul_mem_ringOfIntegers

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Discreteness of the image of the integral lattice under `Phi a`

For a number field `F`, an integer matrix `a : Fin M → Fin N → F`, and the integral lattice
`PLat F N = (𝓞 F)^N ⊆ (KE F)^N` (the product model of the Euclidean mixed space), the image

  `Submodule.map ((Phi a).restrictScalars ℤ) (PLat F N) ⊆ (KE F)^M`

of the integral lattice under the `ℝ`-linear row map
`Phi a y i = ∑_j meK (a i j) * y j` is a discrete `ℤ`-submodule of `(KE F)^M`.

The proof does not need any genericity assumption on `a`: writing `Δ` for the product of
common denominators of the entries of `a`, the key point is that

  `Δ • (Phi a y) = Phi (Δ • a) y ∈ PLat F M` for every `y ∈ PLat F N`,

because `Δ • a` has integral entries and multiplication by an element of `𝓞 F` preserves the
integral lattice.  Hence the scaling map `z ↦ Δ • z` is a continuous injection from the image
lattice into the discrete lattice `PLat F M = (𝓞 F)^M`, which forces the image to be discrete.
-/

set_option linter.style.haveILetI false

open NumberField
open scoped Classical

namespace Work.BW

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ## Discreteness of `PLat F N` -/

/-- The product lattice `PLat F N = (𝓞 F)^N` is discrete: it is a finite product of the
(discrete) Euclidean integral lattices. -/
theorem sieg2PhiImg_PLat_discrete (F : Type*) [Field F] [NumberField F] (N : ℕ) :
    DiscreteTopology ↥(PLat F N) := by
  have hS : ∀ _j : Fin N,
      DiscreteTopology ↥(NumberField.mixedEmbedding.euclidean.integerLattice F) :=
    fun _ => inferInstance
  haveI := hS
  haveI hpi : DiscreteTopology
      (∀ j : Fin N, ↥(NumberField.mixedEmbedding.euclidean.integerLattice F)) := inferInstance
  let f : ↥(PLat F N) → (∀ j : Fin N,
      ↥(NumberField.mixedEmbedding.euclidean.integerLattice F)) :=
    fun x j => ⟨(x : Fin N → KE F) j, (mem_PLat x.1).mp x.2 j⟩
  have hc : Continuous f := by
    apply continuous_pi
    intro j
    exact Continuous.subtype_mk ((continuous_apply j).comp continuous_subtype_val)
      (fun x => (mem_PLat x.1).mp x.2 j)
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext j
    exact congrArg Subtype.val (congrFun hxy j)
  exact DiscreteTopology.of_continuous_injective hc hinj

/-! ## Elementary compatibilities of `meK` with `ℤ`-scalars and finite sums -/

/-- `meK` commutes with integer scaling. -/
theorem sieg2PhiImg_meK_zsmul (m : ℤ) (w : F) : meK (m • w) = m • meK w := by
  simp only [meK, map_zsmul]

/-- `meK` commutes with finite sums. -/
theorem sieg2PhiImg_meK_sum_univ {ι : Type*} [Fintype ι] (f : ι → F) :
    meK (∑ i, f i) = ∑ i, meK (f i) := by
  simp only [meK, map_sum]

/-- Multiplication by `a : F` sends the image of `b` under `meK` to the image of `a * b`. -/
theorem sieg2PhiImg_mulK_meK (a b : F) : mulK a (meK b) = meK (a * b) := by
  simp only [mulK_apply, meK]; simp

/-- `meK` of an algebraic integer lies in the Euclidean integral lattice. -/
theorem sieg2PhiImg_meK_coe_mem_integerLattice (c : 𝓞 F) :
    meK ((c : F)) ∈ NumberField.mixedEmbedding.euclidean.integerLattice F := by
  rw [NumberField.mixedEmbedding.euclidean.integerLattice, ZLattice.comap]
  simp only [Submodule.mem_comap, NumberField.mixedEmbedding.integerLattice,
    LinearMap.mem_range]
  exact ⟨c, rfl⟩

/-- The Euclidean integral lattice of `F` is exactly the image of `𝓞 F` under `meK`. -/
theorem sieg2PhiImg_mem_integerLattice_iff (x : KE F) :
    x ∈ NumberField.mixedEmbedding.euclidean.integerLattice F ↔
      ∃ c : 𝓞 F, meK (c : F) = x := by
  rw [NumberField.mixedEmbedding.euclidean.integerLattice, ZLattice.comap]
  constructor
  · intro hx
    simp only [Submodule.mem_comap, NumberField.mixedEmbedding.integerLattice,
      LinearMap.mem_range] at hx
    obtain ⟨c, hc⟩ := hx
    refine ⟨c, ?_⟩
    rw [meK]
    rw [show NumberField.mixedEmbedding F (algebraMap (𝓞 F) F c) =
      NumberField.mixedEmbedding.euclidean.toMixed F x from hc]
    simp
  · rintro ⟨c, hc⟩
    simp only [Submodule.mem_comap, NumberField.mixedEmbedding.integerLattice,
      LinearMap.mem_range]
    refine ⟨c, ?_⟩
    rw [← hc]
    simp [meK]

/-! ## The scaling computation -/

/-- If every entry `a i j` of `a` has `m * a i j` integral, then for `y` in the integral
lattice `PLat F N` the point `m • (Phi a y)` again lies in the integral lattice `PLat F M`. -/
theorem sieg2PhiImg_smul_Phi_mem_PLat {M N : ℕ} (a : Fin M → Fin N → F) {m : ℤ}
    (hm : ∀ i j, ∃ c : 𝓞 F, (c : F) = (m : F) * a i j)
    {y : Fin N → KE F} (hy : y ∈ PLat F N) :
    m • (Phi a y) ∈ PLat F M := by
  rw [mem_PLat] at hy ⊢
  intro i
  rw [Pi.smul_apply, Phi_apply, Finset.smul_sum]
  choose c hc using fun j => hm i j
  choose β hβ using fun j => (sieg2PhiImg_mem_integerLattice_iff (y j)).mp (hy j)
  have hterm : ∀ j, m • mulK (a i j) (y j) = meK (((c j * β j : 𝓞 F)) : F) := by
    intro j
    rw [← hβ j, sieg2PhiImg_mulK_meK, ← sieg2PhiImg_meK_zsmul]
    congr 1
    calc m • (a i j * ((β j : 𝓞 F) : F))
        = (m : F) * (a i j * ((β j : 𝓞 F) : F)) := zsmul_eq_mul _ _
      _ = ((m : F) * a i j) * ((β j : 𝓞 F) : F) := by ring
      _ = (c j : F) * ((β j : 𝓞 F) : F) := by rw [hc j]
      _ = ((c j * β j : 𝓞 F) : F) := by push_cast; ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  rw [← sieg2PhiImg_meK_sum_univ (fun j => (((c j * β j : 𝓞 F)) : F))]
  have hsum : (∑ j, (((c j * β j : 𝓞 F)) : F)) = ((∑ j, c j * β j : 𝓞 F) : F) :=
    (map_sum (algebraMap (𝓞 F) F) (fun j => c j * β j) Finset.univ).symm
  rw [hsum]
  exact sieg2PhiImg_meK_coe_mem_integerLattice _

/-! ## The main result -/

theorem sieg2_Phi_img_discrete {F : Type*} [Field F] [NumberField F] {M N : ℕ}
    (a : Fin M → Fin N → F) :
    DiscreteTopology ↥(Submodule.map ((Phi a).restrictScalars ℤ) (PLat F N)) := by
  classical
  -- A common (nonzero) integer denominator `mm` for all entries of `a`.
  let e := finProdFinEquiv (m := M) (n := N)
  obtain ⟨mm, hmm_ne, z, hz⟩ := exists_int_mul_mem_ringOfIntegers (F := F)
    (fun p : Fin (M * N) => a (e.symm p).1 (e.symm p).2)
  have hm : ∀ i j, ∃ c : 𝓞 F, (c : F) = (mm : F) * a i j := by
    intro i j
    refine ⟨z (e (i, j)), ?_⟩
    have := hz (e (i, j))
    simpa [e, Equiv.symm_apply_apply] using this
  haveI hPLatM : DiscreteTopology ↥(PLat F M) := sieg2PhiImg_PLat_discrete F M
  set S := Submodule.map ((Phi a).restrictScalars ℤ) (PLat F N) with hS
  -- Scaling by `mm` maps the image lattice into the discrete lattice `PLat F M`.
  have hmem : ∀ x : ↥S, mm • ((x : Fin M → KE F)) ∈ PLat F M := by
    intro x
    obtain ⟨y, hy, hxy⟩ := Submodule.mem_map.mp x.2
    rw [← hxy]
    simpa only [LinearMap.restrictScalars_apply] using sieg2PhiImg_smul_Phi_mem_PLat a hm hy
  have hfcont : Continuous
      (fun x : ↥S => (⟨mm • ((x : Fin M → KE F)), hmem x⟩ : ↥(PLat F M))) := by
    apply Continuous.subtype_mk
    have hcont : Continuous (fun x : ↥S => (mm : ℝ) • ((x : Fin M → KE F))) :=
      continuous_subtype_val.const_smul (mm : ℝ)
    simpa only [Int.cast_smul_eq_zsmul ℝ mm] using hcont
  have hfinj : Function.Injective
      (fun x : ↥S => (⟨mm • ((x : Fin M → KE F)), hmem x⟩ : ↥(PLat F M))) := by
    intro x y hxy
    apply Subtype.ext
    have h2' : (mm : ℝ) • ((x : Fin M → KE F)) = (mm : ℝ) • ((y : Fin M → KE F)) := by
      have hh := congrArg Subtype.val hxy
      simpa only [Int.cast_smul_eq_zsmul ℝ mm] using hh
    have hmR : (mm : ℝ) ≠ 0 := by exact_mod_cast hmm_ne
    have h3 : ((x : Fin M → KE F)) = ((y : Fin M → KE F)) := by
      have := congrArg (fun w : Fin M → KE F => (mm : ℝ)⁻¹ • w) h2'
      simpa [smul_smul, inv_mul_cancel₀ hmR] using this
    exact h3
  exact DiscreteTopology.of_continuous_injective hfcont hfinj

end

end Work.BW
