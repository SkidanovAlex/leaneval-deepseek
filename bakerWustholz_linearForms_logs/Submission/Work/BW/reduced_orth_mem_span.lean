import Mathlib
import Submission.Work.BW.DefsMP
import Submission.Work.BW.zeroDeg_reduce

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If `B` vanishes off `range σ` and `c` is a `ℚ`-basis of `B^⊥ ⊂ ℚ^r` (`c` independent,
orthogonal to `B`), then the `ℚ`-span of the restricted rows `c m ∘ σ` contains every vector
of `ℚ^N'` orthogonal to `B ∘ σ`. -/
theorem reduced_orth_mem_span {r N' : ℕ} (σ : Fin N' → Fin r) (hσ : Function.Injective σ)
    (c : Fin (r - 1) → Fin r → ℚ) (hc : LinearIndependent ℚ c)
    (B : Fin r → ℤ) (hB : B ≠ 0) (hcB : ∀ m, ∑ i, c m i * (B i : ℚ) = 0)
    (hBZ : ∀ k : Fin r, k ∉ Set.range σ → B k = 0)
    (v : Fin N' → ℚ) (hv : ∑ j, (B (σ j) : ℚ) * v j = 0) :
    v ∈ Submodule.span ℚ (Set.range fun m : Fin (r - 1) => fun j : Fin N' => c m (σ j)) := by
  classical
  -- `B ≠ 0` gives a nonzero coordinate, hence `r ≠ 0`.
  obtain ⟨i0, hi0⟩ : ∃ i, B i ≠ 0 := by
    by_contra h
    apply hB
    funext i
    by_contra hne
    exact h ⟨i, hne⟩
  have hr : 0 < r := Nat.lt_of_le_of_lt (Nat.zero_le _) i0.isLt
  -- The linear functional `u ↦ ∑ i, B i * u i` on `ℚ^r`.
  let φ : (Fin r → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun u => ∑ i, (B i : ℚ) * u i
      map_add' := fun a b => by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := fun a b => by
        show (∑ i, (B i : ℚ) * (a * b i)) = a * ∑ i, (B i : ℚ) * b i
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring) }
  have φ_apply : ∀ u : Fin r → ℚ, φ u = ∑ i, (B i : ℚ) * u i := fun u => rfl
  -- `φ` evaluated on the standard basis vector `Pi.single k 1` is `B k`.
  have hφsingle : ∀ k : Fin r, φ (Pi.single k (1:ℚ)) = (B k : ℚ) := by
    intro k
    rw [φ_apply]
    have hk : (B k : ℚ) = (B k : ℚ) * (Pi.single k (1:ℚ) : Fin r → ℚ) k := by
      rw [Pi.single_eq_same, mul_one]
    rw [hk]
    exact Finset.sum_eq_single (f := fun i => (B i : ℚ) * (Pi.single k (1:ℚ) : Fin r → ℚ) i) k
      (fun b _ hb => by simp [hb])
      (fun hk' => absurd (Finset.mem_univ k) hk')
  have hf : φ ≠ 0 := by
    intro h
    have h0 : φ (Pi.single i0 (1:ℚ)) = 0 := by simp [h]
    rw [hφsingle i0] at h0
    exact (Int.cast_ne_zero.mpr hi0) h0
  -- `c` is contained in `ker φ`.
  have hspan_le : Submodule.span ℚ (Set.range c) ≤ φ.ker := by
    rw [Submodule.span_le]
    rintro w ⟨m, rfl⟩
    change c m ∈ φ.ker
    rw [LinearMap.mem_ker, φ_apply]
    rw [Finset.sum_congr rfl (fun i _ => mul_comm ((B i : ℚ)) (c m i)), hcB m]
  have hfin_span : Module.finrank ℚ ↥(Submodule.span ℚ (Set.range c)) = r - 1 := by
    rw [finrank_span_eq_card hc, Fintype.card_fin]
  have hfin_ker : Module.finrank ℚ ↥(φ.ker) = r - 1 := by
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero (f := φ) hf
    rw [Module.finrank_fintype_fun_eq_card ℚ, Fintype.card_fin] at h
    omega
  -- Hence `span c = ker φ` (both are `(r-1)`-dimensional subspaces of `ℚ^r`).
  have hspan_eq : Submodule.span ℚ (Set.range c) = φ.ker :=
    Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [hfin_span, hfin_ker])
  -- Spread `v` to a vector `u` on `Fin r`, supported on `range σ`.
  set u : Fin r → ℚ := ∑ j, v j • (Pi.single (σ j) (1 : ℚ) : Fin r → ℚ) with hu_def
  have hu_apply : ∀ j : Fin N', u (σ j) = v j := by
    intro j
    simp only [hu_def, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hfj : v j * (Pi.single (σ j) (1:ℚ) : Fin r → ℚ) (σ j) = v j := by
      rw [Pi.single_eq_same, mul_one]
    rw [← hfj]
    exact Finset.sum_eq_single (f := fun k => v k * (Pi.single (σ k) (1:ℚ) : Fin r → ℚ) (σ j)) j
      (fun k _ hk => by
        have hjk : σ j ≠ σ k := fun h => hk (hσ h).symm
        simp [hjk])
      (fun hj => absurd (Finset.mem_univ j) hj)
  have hφu : φ u = 0 := by
    simp only [hu_def, map_sum, LinearMap.map_smul, hφsingle]
    rw [show (∑ j, v j • (B (σ j) : ℚ)) = ∑ j, (B (σ j) : ℚ) * v j from
      Finset.sum_congr rfl (fun j _ => by rw [smul_eq_mul, mul_comm]), hv]
  have hu_ker : u ∈ φ.ker := LinearMap.mem_ker.mpr hφu
  have hu_span : u ∈ Submodule.span ℚ (Set.range c) := by
    rw [hspan_eq]; exact hu_ker
  -- Expand `u` in the basis `c`, then restrict to `range σ`.
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (v := c) ℚ).mp hu_span
  have key : ∀ j : Fin N', u (σ j) = ∑ m, a m * c m (σ j) := by
    intro j
    rw [← ha]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hveq : v = ∑ m, a m • (fun j : Fin N' => c m (σ j)) := by
    funext j
    rw [← hu_apply j, key j]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact (Submodule.mem_span_range_iff_exists_fun
      (v := fun m : Fin (r - 1) => fun j : Fin N' => c m (σ j)) ℚ).mpr ⟨a, hveq.symm⟩

end Work.BW
