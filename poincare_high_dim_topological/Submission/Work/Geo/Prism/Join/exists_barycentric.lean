import Mathlib
import Submission.Work.PL.Defs

/-!
# Barycentric coordinates for an affinely independent finite set

Given a nonempty finite set `S : Finset E` of points of a real vector space `E` (viewed as an
affine space over itself) which is affinely independent, we construct affine functionals
`lam s : E →ᵃ[ℝ] ℝ` (`s : S`) forming the barycentric coordinate family of `S`:
`lam s s = 1`, `lam s s' = 0` for `s ≠ s'`, and on the affine span of `S` the coordinates sum to
`1` and reproduce every point as an affine combination.

The construction proceeds directly.  Pick a base point `b₀ ∈ S`; then affine independence of `S`
is linear independence of the differences `s -ᵥ b₀` (`s ≠ b₀`).  A linearly independent family of
values can be extended to a linear functional (`exists_linearMap_prescribed`, via a basis of the
span and `Subspace.dualLift`), which yields for every `s : S` a linear functional `ℓ s` with the
prescribed values on the differences.  Putting `lam s x = ℓ s (x -ᵥ b₀) + cs s` (where
`cs s = 1` if `s = b₀` and `0` otherwise) gives the required family.
-/

open Module Submodule Set Finset

set_option linter.unnecessarySimpa false

namespace Work.Geo.Prism.Join

/-- **Extension of a linear functional from a linearly independent family.**  Given a linearly
independent family `v : ι → V` over `ℝ` and any prescribed values `c : ι → ℝ`, there is a linear
functional on `V` taking the value `c i` at `v i`. -/
theorem exists_linearMap_prescribed {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ι : Type*} (v : ι → V) (hli : LinearIndependent ℝ v) (c : ι → ℝ) :
    ∃ L : V →ₗ[ℝ] ℝ, ∀ i, L (v i) = c i := by
  refine ⟨Subspace.dualLift (Submodule.span ℝ (Set.range v))
      ((Basis.span hli).constr ℝ c), fun i => ?_⟩
  rw [Subspace.dualLift_of_mem (Submodule.subset_span (Set.mem_range_self i))]
  have h : (⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ :
      Submodule.span ℝ (Set.range v)) = Basis.span hli i := (Basis.span_apply hli i).symm
  rw [h, Basis.constr_basis]

set_option linter.unusedSimpArgs false in
/-- **Barycentric coordinates of an affinely independent finite set.**  For a nonempty finite
affinely independent set `S` in a real vector space `E` (affine over itself) there is a family of
affine functionals which is the Kronecker delta on `S` and which gives barycentric coordinates on
the affine span of `S`. -/
theorem exists_barycentric_general (E : Type*) [AddCommGroup E] [Module ℝ E]
    (S : Finset E) (hS : S.Nonempty)
    (hind : AffineIndependent ℝ (fun v : S => (v : E))) :
    ∃ lam : S → (E →ᵃ[ℝ] ℝ),
      (∀ s, lam s s = 1) ∧ (∀ s s', s ≠ s' → lam s s' = 0) ∧
      (∀ x ∈ (affineSpan ℝ (S : Set E) : Set E),
        (∑ s : S, lam s x) = 1 ∧ (∑ s : S, (lam s x) • (s : E)) = x) := by
  classical
  obtain ⟨b, hb⟩ := hS
  set b₀ : S := ⟨b, hb⟩ with hb₀def
  have hli : LinearIndependent ℝ
      (fun t : {t : S // t ≠ b₀} => (t.1 : E) -ᵥ (b₀ : E)) := by
    have h := (affineIndependent_iff_linearIndependent_vsub ℝ (fun v : S => (v : E)) b₀).mp hind
    simpa using h
  let vals : S → ({t : S // t ≠ b₀} → ℝ) := fun s t =>
    (if (t.1 : S) = s then (1:ℝ) else 0) - (if s = b₀ then (1:ℝ) else 0)
  have hLmap : ∀ c : {t : S // t ≠ b₀} → ℝ,
      ∃ L : E →ₗ[ℝ] ℝ, ∀ t, L ((t.1 : E) -ᵥ (b₀ : E)) = c t :=
    fun c => exists_linearMap_prescribed _ hli c
  let ℓ : S → (E →ₗ[ℝ] ℝ) := fun s => (hLmap (vals s)).choose
  have hℓ : ∀ s t, ℓ s ((t.1 : E) -ᵥ (b₀ : E)) = vals s t :=
    fun s t => (hLmap (vals s)).choose_spec t
  let cs : S → ℝ := fun s => if s = b₀ then 1 else 0
  let lam : S → (E →ᵃ[ℝ] ℝ) := fun s =>
    AffineMap.mk' (fun x => ℓ s (x -ᵥ (b₀ : E)) + cs s) (ℓ s) (b₀ : E)
      (fun p' => by simp)
  have hlam_apply : ∀ s x, lam s x = ℓ s (x -ᵥ (b₀ : E)) + cs s := fun s x => rfl
  let L : E →ₗ[ℝ] ℝ := ∑ s : S, ℓ s
  let T : E →ₗ[ℝ] E := ∑ s : S, (ℓ s).smulRight ((s : E) -ᵥ (b₀ : E))
  have hLgen : ∀ t : {t : S // t ≠ b₀}, L ((t.1 : E) -ᵥ (b₀ : E)) = 0 := by
    intro t
    have h1 : L ((t.1 : E) -ᵥ (b₀ : E)) = ∑ s : S, ℓ s ((t.1 : E) -ᵥ (b₀ : E)) := by simp [L]
    rw [h1]
    have h2 : ∀ s : S, ℓ s ((t.1 : E) -ᵥ (b₀ : E)) = vals s t := fun s => hℓ s t
    simp_rw [h2]
    simp only [vals]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    simp
  have hTgen : ∀ t : {t : S // t ≠ b₀},
      T ((t.1 : E) -ᵥ (b₀ : E)) = (t.1 : E) -ᵥ (b₀ : E) := by
    intro t
    have h1 : T ((t.1 : E) -ᵥ (b₀ : E)) =
        ∑ s : S, ℓ s ((t.1 : E) -ᵥ (b₀ : E)) • ((s : E) -ᵥ (b₀ : E)) := by simp [T]
    rw [h1]
    have h2 : ∀ s : S, ℓ s ((t.1 : E) -ᵥ (b₀ : E)) • ((s : E) -ᵥ (b₀ : E))
        = vals s t • ((s : E) -ᵥ (b₀ : E)) := fun s => by rw [hℓ s t]
    simp_rw [h2]
    simp only [vals]
    simp_rw [sub_smul, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq']
    simp
  refine ⟨lam, ?_, ?_, ?_⟩
  · intro s
    rw [hlam_apply]
    by_cases hs : s = b₀
    · subst hs; simp [cs]
    · show (ℓ s) (((⟨s, hs⟩ : {t : S // t ≠ b₀}).1 : E) -ᵥ (b₀ : E)) + cs s = 1
      rw [hℓ]
      simp only [vals]
      simp [hs, cs]
  · intro s s' hss
    rw [hlam_apply]
    by_cases hs' : s' = b₀
    · subst hs'
      rw [vsub_self, map_zero]
      have hsne : s ≠ b₀ := fun h => hss h
      simp [cs, hsne]
    · show (ℓ s) (((⟨s', hs'⟩ : {t : S // t ≠ b₀}).1 : E) -ᵥ (b₀ : E)) + cs s = 0
      rw [hℓ]
      simp only [vals]
      by_cases hs : s = b₀
      · subst hs
        simp [cs]
        exact hs'
      · have hne : ((⟨s', hs'⟩ : {t : S // t ≠ b₀}).1 : S) ≠ s := by
          intro h; exact hss h.symm
        simp [cs, hs, hne]
  · intro x hx
    have hy : x -ᵥ (b₀ : E) ∈
        Submodule.span ℝ (Set.range (fun t : {t : S // t ≠ b₀} => (t.1 : E) -ᵥ (b₀ : E))) := by
      have hbA : (b₀ : E) ∈ affineSpan ℝ (S : Set E) :=
        subset_affineSpan ℝ (S : Set E) (by simpa using hb)
      have hdir : x -ᵥ (b₀ : E) ∈ (affineSpan ℝ (S : Set E)).direction :=
        AffineSubspace.vsub_mem_direction hx hbA
      rw [direction_affineSpan] at hdir
      rw [show (S : Set E) = Set.range (fun s : S => (s : E)) from (Subtype.range_coe).symm] at hdir
      rw [vectorSpan_range_eq_span_range_vsub_right_ne ℝ (fun s : S => (s : E)) b₀] at hdir
      exact hdir
    have hLy : L (x -ᵥ (b₀ : E)) = 0 := LinearMap.mem_ker.mp
      (Submodule.span_le.mpr (by rintro y ⟨t, rfl⟩; exact LinearMap.mem_ker.mpr (hLgen t)) hy)
    have hTy : T (x -ᵥ (b₀ : E)) = x -ᵥ (b₀ : E) := by
      have h := (Submodule.span_le.mpr (by
        rintro y ⟨t, rfl⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
          hTgen t, sub_self]) :
        Submodule.span ℝ (Set.range (fun t : {t : S // t ≠ b₀} => (t.1 : E) -ᵥ (b₀ : E))) ≤
          LinearMap.ker (T - LinearMap.id)) hy
      simpa only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] using h
    have hLx : (∑ s : S, ℓ s (x -ᵥ (b₀ : E))) = 0 := by
      have : (∑ s : S, ℓ s (x -ᵥ (b₀ : E))) = L (x -ᵥ (b₀ : E)) := by simp [L]
      rw [this, hLy]
    have hcs : (∑ s : S, cs s) = 1 := by
      simp only [cs]
      rw [Finset.sum_ite_eq']
      simp
    constructor
    · have hsum1 : (∑ s : S, lam s x) = ∑ s : S, (ℓ s (x -ᵥ (b₀ : E)) + cs s) :=
        Finset.sum_congr rfl (fun s _ => hlam_apply s x)
      rw [hsum1, Finset.sum_add_distrib, hLx, hcs, zero_add]
    · have hsum2 : (∑ s : S, (lam s x) • (s : E)) =
          ∑ s : S, (ℓ s (x -ᵥ (b₀ : E)) + cs s) • ((b₀ : E) + ((s : E) -ᵥ (b₀ : E))) :=
        Finset.sum_congr rfl (fun s _ => by
          rw [hlam_apply s x]
          congr 1
          rw [add_comm, ← vadd_eq_add, vsub_vadd])
      rw [hsum2]
      simp_rw [smul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_smul]
      have hsum3 : (∑ s : S, (ℓ s (x -ᵥ (b₀ : E)) + cs s)) = 1 := by
        rw [Finset.sum_add_distrib, hLx, hcs, zero_add]
      rw [hsum3, one_smul]
      simp_rw [add_smul]
      rw [Finset.sum_add_distrib]
      have hTy' : (∑ s : S, ℓ s (x -ᵥ (b₀ : E)) • ((s : E) -ᵥ (b₀ : E))) = x -ᵥ (b₀ : E) := by
        have : (∑ s : S, ℓ s (x -ᵥ (b₀ : E)) • ((s : E) -ᵥ (b₀ : E))) = T (x -ᵥ (b₀ : E)) :=
          by simp [T]
        rw [this, hTy]
      have hcs2 : (∑ s : S, cs s • ((s : E) -ᵥ (b₀ : E))) = 0 := by
        simp only [cs]
        simp_rw [ite_smul, one_smul, zero_smul]
        rw [Finset.sum_ite_eq']
        simp
      rw [hTy', hcs2, add_zero]
      rw [add_comm, ← vadd_eq_add, vsub_vadd]

/-- Barycentric coordinates for an affinely independent finite set of points of `PL.E n`. -/
lemma exists_barycentric (n : ℕ) (S : Finset (PL.E n)) (hS : S.Nonempty)
    (hind : AffineIndependent ℝ (fun v : S => (v : PL.E n))) :
    ∃ lam : S → (PL.E n →ᵃ[ℝ] ℝ),
      (∀ s, lam s s = 1) ∧ (∀ s s', s ≠ s' → lam s s' = 0) ∧
      (∀ x ∈ (affineSpan ℝ (S : Set (PL.E n)) : Set (PL.E n)),
        (∑ s : S, lam s x) = 1 ∧ (∑ s : S, (lam s x) • (s : PL.E n)) = x) :=
  exists_barycentric_general (PL.E n) S hS hind

end Work.Geo.Prism.Join
