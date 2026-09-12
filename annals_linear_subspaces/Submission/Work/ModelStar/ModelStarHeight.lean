import Mathlib
import ChallengeDeps
import Submission.GeometryOfNumbers.Heights
import Submission.GeometryOfNumbers.PlaneFinrank
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul

/-!
# Height half of the model ★-pair, first stone: `height V ≤ ‖ιMulti u‖`

`ModelStar.modelStar_distance` produces the ★-pair **distance** half: a plane
`V = span ℝ (range m)` of integer preimages with `distSubspaces V (modelX ℓ) ≤
(1/(1−k/5))·e^{−t(1/ℓ+1/(d−ℓ))}`.  The ★-pair **height** half needs, for the same plane,
`height V ≤ C·e^{t·k/ℓ}`.  The first generic stone (ROADMAP (a1), route B — the integer
change-of-basis route, chosen after the record of the two candidate routes) is the
submodule-free inequality proved here:

**`height_le_norm_iMulti_of_mem_imageLattice`** — for a rational subspace `V` and an
ℝ-independent family `u : Fin (finrank ℝ V) → ℝᵈ` of integer points of `V` (`u j ∈
imageLattice V = V ∩ ℤᵈ`):

    `height V hV ≤ ‖ιMulti ℝ (finrank ℝ V) u‖`

(the height of `V` — the covolume of `V ∩ ℤᵈ`, realised as the norm of the wedge of a
ℤ-basis of that lattice — is at most the norm of the wedge of ANY integer family that
spans it: a superlattice has no larger covolume than any of its sublattices).

Proof (route B): with `u' := cbFamily V hV` the ℤ-basis of the image lattice
(`chosenBasis_span_lattice`), each `u j ∈ span ℤ (range u')` (`mem_span_range_iff_exists_fun`
over `ℤ`) gives integer coefficients `cf j i` with `u j = ∑ᵢ (cf j i) • u' i` (the canonical
integer action agrees with smul by the real cast — `real_natCast_smul`/`int_smul_eq_real`,
proved by induction).  The integer matrix `A' i j := cf j i` (cast to `A` over `ℝ`)
satisfies the column-combination hypothesis of the Commons determinant lemma
`iMulti_det_smul`, giving `ιMulti u = det A • ιMulti u'`.  The wedge of the independent
family `u` is non-zero (`iMulti_ne_zero_of_linearIndependent`), so `det A ≠ 0`; since
`det A = (det A' : ℝ)` (`RingHom.map_det`) and `det A'` is an integer, `|det A| ≥ 1`
(`Int.one_le_abs`).  Therefore `height = ‖ιMulti u'‖ ≤ |det A|·‖ιMulti u'‖ = ‖ιMulti u‖`.

This is generic and submodule-relative only through `V`, `hV`, `imageLattice`, `cbFamily`;
it is reused verbatim by the general-`x` (s_x) machinery later.  The application step to
the ★-pair (reindex `m : Fin k → ℤᵈ` to `Fin (finrank V)`, then feed the diagonal bound
`‖mᵢ‖ ≤ 12·ℓ` / `prop5_model_log_upper_slope` to get `height ≤ C·e^{t·k/ℓ}`) is the next
stone.
-/

noncomputable section
open Module exteriorPower InnerProductGeometry
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open LinearSubspaces

namespace Submission.ModelStarHeight

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-- The real scalar action of a natural agrees with the canonical natural action. -/
lemma real_natCast_smul (x : ℝᵈ) (n : ℕ) : (n : ℝ) • x = n • x := by
  induction n with
  | zero => simp
  | succ n ih => simp [Nat.cast_succ, add_smul, ih]

/-- The canonical integer action of `z` on a real vector agrees with smul by the real cast. -/
lemma int_smul_eq_real (x : ℝᵈ) (z : ℤ) : z • x = (z : ℝ) • x := by
  rcases z.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simp [natCast_zsmul, real_natCast_smul]
  · simp [Int.cast_neg, natCast_zsmul, real_natCast_smul]

/-- An integer point of `V` (in `ℤᵈ`) lies in the image lattice `V ∩ ℤᵈ`. -/
lemma mem_imageLattice_of_mem (V : Submodule ℝ ℝᵈ) {x : ℝᵈ} (hxV : x ∈ V)
    (hxZ : x ∈ intPoints (d := d)) : x ∈ Submission.Heights.imageLattice (d := d) V := by
  classical
  dsimp [Submission.Heights.imageLattice]
  rw [Submodule.mem_map]
  refine ⟨⟨x, hxV⟩, ?_, ?_⟩
  · dsimp [intPointsSubspace, ZLattice.comap]
    rw [Submodule.mem_comap]
    simpa using hxZ
  · rfl

/-- **Height ≤ norm of any integer wedge**: if `u` is an ℝ-independent family of integer
points of the rational subspace `V` (i.e. `u j ∈ imageLattice V = V ∩ ℤᵈ`), of the right
cardinality `finrank ℝ V`, then `height V hV ≤ ‖ιMulti u‖`.  Proof: with `u' := cbFamily V
hV` a ℤ-basis of the image lattice, each `u j ∈ span ℤ (range u')` gives an integer change
matrix `A` (`u = u'·A`), so `ιMulti u = det A • ιMulti u'` (Commons
`iMulti_det_smul`); `det A` is a non-zero integer (the wedge of the independent `u` is
non-zero), hence `|det A| ≥ 1` and `height = ‖ιMulti u'‖ ≤ |det A|·‖ιMulti u'‖ =
‖ιMulti u‖`. -/
theorem height_le_norm_iMulti_of_mem_imageLattice (V : Submodule ℝ ℝᵈ) (hV : IsRational V)
    (u : Fin (Module.finrank ℝ V) → ℝᵈ)
    (hu_mem : ∀ j, u j ∈ Submission.Heights.imageLattice (d := d) V)
    (hu_li : LinearIndependent ℝ u) :
    LinearSubspaces.height V hV ≤ ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V) u‖ := by
  classical
  let k : ℕ := Module.finrank ℝ V
  let u' : Fin k → ℝᵈ := Submission.Heights.cbFamily (d := d) V hV
  have hspanZ : Submodule.span ℤ (Set.range u') = Submission.Heights.imageLattice (d := d) V := by
    dsimp [u']
    exact Submission.Heights.chosenBasis_span_lattice (d := d) V hV
  -- integer coefficients: u j = Σ cf j i • u' i  (ℤ-smul)
  have hmemZ : ∀ j : Fin k, u j ∈ Submodule.span ℤ (Set.range u') := by
    intro j
    rw [hspanZ]
    exact hu_mem j
  let cf : Fin k → Fin k → ℤ := fun j =>
    Classical.choose ((Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := u') (x := u j)).mp (hmemZ j))
  have hcf_spec : ∀ j : Fin k, (∑ i : Fin k, cf j i • u' i) = u j := by
    intro j
    exact Classical.choose_spec ((Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := u') (x := u j)).mp (hmemZ j))
  have hcf : ∀ j : Fin k, u j = ∑ i : Fin k, cf j i • u' i := fun j => (hcf_spec j).symm
  -- integer matrix and its real cast
  let A' : Matrix (Fin k) (Fin k) ℤ := fun i j => cf j i
  let A : Matrix (Fin k) (Fin k) ℝ := fun i j => ((cf j i : ℤ) : ℝ)
  have hwA : ∀ j : Fin k, u j = ∑ i : Fin k, A i j • u' i := by
    intro j
    rw [hcf j]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [A]
    exact int_smul_eq_real (u' i) (cf j i)
  have hdets : exteriorPower.ιMulti ℝ k u = A.det • exteriorPower.ιMulti ℝ k u' := by
    exact Commons.LinearAlgebra.ExteriorPower.iMulti_det_smul (K := ℝ) (u := u') (A := A)
      (w := u) hwA
  -- det A ≠ 0 (the wedge of u is non-zero)
  have hu0 : exteriorPower.ιMulti ℝ k u ≠ 0 :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_ne_zero_of_linearIndependent (K := ℝ) u hu_li
  have hdet_ne0 : A.det ≠ 0 := by
    intro hd0
    apply hu0
    rw [hdets, hd0, zero_smul]
  -- det A is a non-zero integer, so |det A| ≥ 1
  have hAint : A.det = (A'.det : ℝ) := by
    let f : ℤ →+* ℝ := Int.castRingHom (α := ℝ)
    have hmap := RingHom.map_det f A'
    have hAeq : A = f.mapMatrix A' := by
      ext i j
      rfl
    calc
      A.det = (f.mapMatrix A').det := by rw [hAeq]
      _ = f A'.det := hmap.symm
      _ = (A'.det : ℝ) := by rfl
  have hA'det_ne0 : A'.det ≠ 0 := by
    intro hz
    apply hdet_ne0
    rw [hAint]
    exact_mod_cast hz
  have hAbs : (1 : ℝ) ≤ |A.det| := by
    rw [hAint]
    rw [← Int.cast_abs]
    exact_mod_cast (Int.one_le_abs hA'det_ne0)
  -- height = ‖ιMulti u'‖
  have hH : LinearSubspaces.height V hV = ‖exteriorPower.ιMulti ℝ k u'‖ := by
    dsimp [u', Submission.Heights.cbFamily]
    rfl
  calc
    LinearSubspaces.height V hV = ‖exteriorPower.ιMulti ℝ k u'‖ := hH
    _ ≤ |A.det| * ‖exteriorPower.ιMulti ℝ k u'‖ := by
          simpa using (mul_le_mul_of_nonneg_right hAbs
            (norm_nonneg (exteriorPower.ιMulti ℝ k u')))
    _ = ‖A.det • exteriorPower.ιMulti ℝ k u'‖ := by
          rw [norm_smul (r := A.det) (x := exteriorPower.ιMulti ℝ k u')]
          simp
    _ = ‖exteriorPower.ιMulti ℝ k u‖ := by
          rw [← hdets]

/-- **Height ≤ wedge norm of an integer spanning family (reindexed form)**: if
`V = span ℝ (range m)` for an ℝ-independent family `m : Fin k → ℝᵈ` of integer points,
then (reindexing `m` along `Fin.cast` of `finrank ℝ V = k`) the height bound of
`height_le_norm_iMulti_of_mem_imageLattice` reads

    `height V hV ≤ ‖ιMulti ℝ (finrank ℝ V) u‖`,   `u i := m (Fin.cast hfin i)`.

All hypotheses transfer to the reindexed family: membership in `imageLattice V`
(`mem_imageLattice_of_mem`: `u j ∈ V` since `m j ∈ range m ⊆ V`, and `u j ∈ ℤᵈ`), and
ℝ-independence (`LinearIndependent.comp` through the injective `Fin.cast`).  The norms
stay on the `Fin (finrank V)` side, so no cross-type exterior-power transport is needed;
products over `Fin (finrank V)` have the same cardinality `k`. -/
theorem height_le_span_intPoints {k : ℕ} (V : Submodule ℝ ℝᵈ) (hV : IsRational V)
    {m : Fin k → ℝᵈ} (hspan : Submodule.span ℝ (Set.range m) = V)
    (hmem : ∀ i, m i ∈ intPoints (d := d)) (hLI : LinearIndependent ℝ m) :
    LinearSubspaces.height V hV ≤
      ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V)
        (fun i : Fin (Module.finrank ℝ V) => m
          (Fin.cast (by rw [← hspan]; exact PlaneFinrank.finrank_span_range (d := d) m hLI) i))‖ := by
  classical
  have hfin : Module.finrank ℝ V = k := by
    rw [← hspan]
    exact PlaneFinrank.finrank_span_range (d := d) m hLI
  let u : Fin (Module.finrank ℝ V) → ℝᵈ := fun i => m (Fin.cast hfin i)
  have hu_mem : ∀ j, u j ∈ Submission.Heights.imageLattice (d := d) V := by
    intro j
    apply mem_imageLattice_of_mem V
    · dsimp [u]
      have hmemV : m (Fin.cast hfin j) ∈ Submodule.span ℝ (Set.range m) :=
        Submodule.subset_span ⟨Fin.cast hfin j, rfl⟩
      rw [hspan] at hmemV
      exact hmemV
    · dsimp [u]
      exact hmem (Fin.cast hfin j)
  have hu_li : LinearIndependent ℝ u := by
    dsimp [u]
    exact LinearIndependent.comp hLI (Fin.cast hfin) (Fin.cast_injective hfin)
  have hmain := height_le_norm_iMulti_of_mem_imageLattice (d := d) V hV u hu_mem hu_li
  simpa [u, hfin] using hmain

end Submission.ModelStarHeight
