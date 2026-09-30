import Mathlib
import Submission.Work.BW.DefsMult

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- **Saturation of the row lattice (Baker–Wüstholz).** If the rows of the integer matrix `M` form a
primitive system -- `ℚ`-linearly independent with `ℤ`-span saturated in `ℤ^N` -- then the vector
`u : ℤ^N` lies in the `ℤ`-span of the rows as soon as its image in `ℚ^N` lies in the `ℚ`-span of
the rows. Contrapositively, an integral vector outside the row lattice is not in the rational row
space. This is the linear-algebra fact behind the saturation hypothesis in `PrimSys`. -/
lemma ratSpan_saturation {N ρ : ℕ} (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M) (u : Fin N → ℤ)
    (hu : ¬ ∃ c : Fin ρ → ℤ, ∀ i, u i = ∑ j, c j * M j i) :
    (fun i => (u i : ℚ)) ∉ Submodule.span ℚ (Set.range (fun j => fun i => (M j i : ℚ))) := by
  classical
  intro hu0
  -- Extract a rational representation `u = ∑ q_j M_j`.
  rw [Submodule.mem_span_range_iff_exists_fun ℚ] at hu0
  obtain ⟨q, hq⟩ := hu0
  have hqc : ∀ i, ∑ j, q j * (M j i : ℚ) = (u i : ℚ) := by
    intro i
    have h := congr_fun hq i
    simpa using h
  -- A common denominator for the coefficients `q j`.
  let m0 : ℕ := ∏ j, (q j).den
  have hm0ne : m0 ≠ 0 := by
    dsimp only [m0]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => Rat.den_nz _)
  -- Rescale the coefficients to integers.
  let a : Fin ρ → ℤ := fun j => ((m0 / (q j).den : ℕ) : ℤ) * (q j).num
  have haq : ∀ j, (a j : ℚ) = (((m0 : ℤ) : ℚ)) * q j := by
    intro j
    have hdvd : (q j).den ∣ m0 := by
      dsimp only [m0]; exact Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
    have hsplit : (((m0 : ℤ) : ℚ)) = ((m0 / (q j).den : ℕ) : ℚ) * ((q j).den : ℚ) := by
      rw [Int.cast_natCast, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
    calc (a j : ℚ) = ((m0 / (q j).den : ℕ) : ℚ) * ((q j).num : ℚ) := by
          simp only [a]; rw [Int.cast_mul, Int.cast_natCast]
      _ = ((m0 / (q j).den : ℕ) : ℚ) * (((q j).den : ℚ) * q j) := by rw [Rat.den_mul_eq_num]
      _ = (((m0 : ℤ) : ℚ)) * q j := by rw [hsplit]; ring
  -- Thus `m0 • u` is an integral combination of the rows.
  have key : (m0 : ℤ) • u = ∑ j, a j • M j := by
    funext i
    rw [Pi.smul_apply, Finset.sum_apply]
    change (m0 : ℤ) * u i = ∑ j, a j * M j i
    refine Int.cast_injective (α := ℚ) ?_
    show (((m0 : ℤ) * u i : ℤ) : ℚ) = ((∑ j, a j * M j i : ℤ) : ℚ)
    rw [Int.cast_mul, Int.cast_sum]
    rw [← hqc i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Int.cast_mul, haq j]
    ring
  have hmem : (m0 : ℤ) • u ∈ Submodule.span ℤ (Set.range M) := by
    rw [key]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ (a j)
      (Submodule.subset_span (Set.mem_range_self j)))
  -- Saturation upgrades `m0 • u ∈ 𝒵` to `u ∈ 𝒵`.
  have hspan : u ∈ Submodule.span ℤ (Set.range M) :=
    hM.2 u (m0 : ℤ) (Nat.cast_ne_zero.mpr hm0ne) hmem
  rw [Submodule.mem_span_range_iff_exists_fun ℤ] at hspan
  obtain ⟨c, hc⟩ := hspan
  exact hu ⟨c, fun i => by
    have h := congr_fun hc i
    simp only [Pi.smul_apply, Finset.sum_apply] at h
    exact h.symm⟩

end Work.BW
