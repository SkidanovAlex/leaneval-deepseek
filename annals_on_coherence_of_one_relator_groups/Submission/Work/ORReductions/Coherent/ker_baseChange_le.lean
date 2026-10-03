import Mathlib

namespace Work.ORReductions.Coherent

/-- If the basis `bS` of the `R`-module `S` commutes with the image of `f`, then right
multiplication by `f r` in `S` corresponds, in the coordinates given by `bS`, to multiplying the
coefficients by `r` on the right. -/
private lemma repr_symm_mapRange_mul {R S : Type*} [Ring R] [Ring S] (f : R →+* S) [Module R S]
    (hsmul : ∀ (r : R) (s : S), r • s = f r * s)
    {ι : Type*} (bS : Module.Basis ι R S)
    (hc : ∀ (j : ι) (r : R), bS j * f r = f r * bS j)
    (γ : ι →₀ R) (r : R) :
    bS.repr.symm (γ.mapRange (fun a => a * r) (by simp)) = bS.repr.symm γ * f r := by
  rw [Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply, Module.Basis.repr_symm_apply,
    Finsupp.linearCombination_apply]
  rw [Finsupp.sum_mapRange_index (by intro a; simp)]
  rw [Finsupp.sum_mul]
  exact Finsupp.sum_congr fun j _ => by
    rw [hsmul (γ j * r) (bS j), hsmul (γ j) (bS j), map_mul]
    simp only [mul_assoc]
    rw [hc j r]

theorem ker_baseChange_le {R S : Type*} [Ring R] [Ring S] (f : R →+* S) [Module R S]
    (hsmul : ∀ (r : R) (s : S), r • s = f r * s)
    {ι : Type*} (bS : Module.Basis ι R S)
    (hc : ∀ (j : ι) (r : R), bS j * f r = f r * bS j)
    {n m : ℕ} (v : Fin n → R) (w : Fin m → (Fin n →₀ R))
    (hw : Submodule.span R (Set.range w) = LinearMap.ker (Finsupp.linearCombination R v)) :
    LinearMap.ker (Finsupp.linearCombination S (fun i => f (v i))) ≤
      Submodule.span S (Set.range (fun k => Finsupp.mapRange f (map_zero f) (w k))) := by
  classical
  intro y hy
  rw [LinearMap.mem_ker] at hy
  -- the coordinates of `y` in the basis `bS`
  set c : Fin n → (ι →₀ R) := fun i => bS.repr (y i) with hcdef
  have hy_eq : ∀ i : Fin n, y i = bS.repr.symm (c i) := by
    intro i
    simp [hcdef]
  -- the relation `y` satisfies, written as a sum over `Fin n`
  have hy_sum : ∑ i : Fin n, y i * f (v i) = 0 := by
    have h := hy
    rw [Finsupp.linearCombination_apply] at h
    rw [← h, Finsupp.sum_of_support_subset y (Finset.subset_univ _)
      (fun i a => a • f (v i)) (by intro i _; simp)]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_eq_mul]
  -- the transposed element: its `j`-th coefficient is the `j`-th column of the coordinate matrix
  set W : ι →₀ R := ∑ i : Fin n, (c i).mapRange (fun a => a * v i) (by simp) with hWdef
  have hW_apply : ∀ j : ι, W j = ∑ i : Fin n, (c i) j * v i := by
    intro j
    rw [hWdef, Finsupp.finsetSum_apply]
    simp [Finsupp.mapRange_apply]
  have hW0 : W = 0 := by
    have h1 : bS.repr.symm W = ∑ i : Fin n, y i * f (v i) := by
      rw [hWdef, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [repr_symm_mapRange_mul f hsmul bS hc, hy_eq i]
    refine bS.repr.symm.injective ?_
    rw [h1, hy_sum]
    simp
  -- every column of the coordinate matrix lies in the kernel over `R`
  have hcol : ∀ j : ι, (Finsupp.onFinset (Finset.univ : Finset (Fin n)) (fun i => (c i) j)
      (fun i _ => Finset.mem_univ i)) ∈ Submodule.span R (Set.range w) := by
    intro j
    rw [hw, LinearMap.mem_ker, Finsupp.linearCombination_apply]
    rw [Finsupp.sum_of_support_subset _ (Finset.subset_univ _) (fun i a => a • v i)
      (by intro i _; simp)]
    simp only [Finsupp.onFinset_apply, smul_eq_mul]
    rw [← hW_apply j, hW0]
    simp
  -- so each column is an `R`-linear combination of the `w l`
  have hcoeff : ∀ j : ι, ∃ a : Fin m → R, ∀ i : Fin n,
      (∑ l : Fin m, a l * (w l) i) = (c i) j := by
    intro j
    have hmem := hcol j
    rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨a, ha⟩ := hmem
    refine ⟨a, fun i => ?_⟩
    have h1 : (∑ l : Fin m, a l • w l) i = ∑ l : Fin m, a l * (w l) i := by
      rw [Finsupp.finsetSum_apply]
      simp [Finsupp.smul_apply]
    rw [← h1, ha, Finsupp.onFinset_apply]
  choose α hα using hcoeff
  -- the finite set of coordinates that are actually needed
  set J : Finset ι := Finset.univ.biUnion (fun i : Fin n => (c i).support) with hJ
  set s : Fin m → S := fun l => ∑ j ∈ J, f (α j l) * bS j with hs
  have hmain : y = ∑ l : Fin m, s l • Finsupp.mapRange f (map_zero f) (w l) := by
    refine Finsupp.ext fun i => ?_
    have hsub : (c i).support ⊆ J := by
      rw [hJ]
      exact Finset.subset_biUnion_of_mem (fun i : Fin n => (c i).support) (Finset.mem_univ i)
    have h1 : y i = ∑ j ∈ J, (c i) j • bS j := by
      rw [hy_eq i, Module.Basis.repr_symm_apply, Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset (c i) hsub (fun j a => a • bS j) (by intro j _; simp)]
    have h2 : ∑ j ∈ J, (c i) j • bS j =
        ∑ j ∈ J, ∑ l : Fin m, (α j l * (w l) i) • bS j := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← hα j i, Finset.sum_smul]
    have h3 : ∑ j ∈ J, ∑ l : Fin m, (α j l * (w l) i) • bS j =
        ∑ j ∈ J, ∑ l : Fin m, (f (α j l) * bS j) * f ((w l) i) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      rw [hsmul (α j l * (w l) i) (bS j), map_mul]
      simp only [mul_assoc]
      rw [hc j ((w l) i)]
    have h4 : ∑ j ∈ J, ∑ l : Fin m, (f (α j l) * bS j) * f ((w l) i) =
        ∑ l : Fin m, ∑ j ∈ J, (f (α j l) * bS j) * f ((w l) i) :=
      Finset.sum_comm
    have h5 : ∑ l : Fin m, ∑ j ∈ J, (f (α j l) * bS j) * f ((w l) i) =
        ∑ l : Fin m, s l * f ((w l) i) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [hs, Finset.sum_mul]
    have h6 : ∑ l : Fin m, s l * f ((w l) i) =
        (∑ l : Fin m, s l • Finsupp.mapRange f (map_zero f) (w l)) i := by
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    rw [h1, h2, h3, h4, h5]
    exact h6
  rw [hmain]
  exact Submodule.sum_mem _ fun l _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self l))

end Work.ORReductions.Coherent
