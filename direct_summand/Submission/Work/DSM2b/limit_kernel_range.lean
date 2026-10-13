import Mathlib
import Submission.Work.DSM2b.FlatSetup
import Submission.Work.DSG4b.series_limit_of_pow_mem

/-!
# The limit step of Bhatt's Proposition 4.1 (flat part)

Suppose `B` is `π`-adically complete, `φ : B^t → B^l` is `B`-linear, and the preimage under `φ` of
`π ^ N B^l` is contained in `ker φ + π ^ (N - c) B^t` for a fixed constant `c` (this is the
Artin–Rees refined syzygy statement supplied by `Work.DSM2b.syzygy_mod_pow`).  Then `φ` computes
the *closed* image: if `u ∈ B^l` is congruent to an element of `range φ` modulo `π ^ N` for every
`N`, then `u ∈ range φ`.

The proof is the classical Mittag-Leffler/patching argument: pick `z_N` with
`u - φ z_N ∈ π ^ N B^l`, correct `z_N` by elements of `ker φ` so that the corrected sequence
`z'_N` has increments in `π ^ (N - c) B^t` while keeping `φ z'_N = φ z_N`; the sequence converges
`π`-adically by `Work.DSG4b.series_limit_of_pow_mem`, and the limit `ζ` satisfies `φ ζ = u` by
Hausdorffness.
-/

namespace Work.DSM2b

universe u

/-- **Limit step.**  Let `B` be `π`-adically complete, `φ : B^t → B^l` linear over `B`, and
suppose that for every `N` an element `z` with `φ z ∈ π ^ N B^l` differs from an element of
`ker φ` by something in `π ^ (N - c) B^t`.  Then an element `u` of `B^l` which is congruent to
`range φ` modulo `π ^ N` for every `N` lies in `range φ`. -/
theorem mem_range_of_forall_sub_mem {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] (π : R)
    [IsAdicComplete (Ideal.span {algebraMap R B π}) B] {t l : ℕ}
    (φ : (Fin t → B) →ₗ[B] (Fin l → B)) (c : ℕ)
    (hc : ∀ N (z : Fin t → B), (∀ i, φ z i ∈ Ideal.span {algebraMap R B π} ^ N) →
      ∃ w ∈ LinearMap.ker φ, ∀ i, (z - w) i ∈ Ideal.span {algebraMap R B π} ^ (N - c))
    (u : Fin l → B)
    (hu : ∀ N, ∃ z : Fin t → B, ∀ i, (u - φ z) i ∈ Ideal.span {algebraMap R B π} ^ N) :
    u ∈ LinearMap.range φ := by
  classical
  obtain ⟨z, hz⟩ : ∃ z : ℕ → (Fin t → B), ∀ N i, (u - φ (z N)) i ∈
      Ideal.span {algebraMap R B π} ^ N := by
    choose z hz using hu
    exact ⟨z, hz⟩
  have hinc : ∀ N, ∃ w : Fin t → B, w ∈ LinearMap.ker φ ∧
      ∀ i, ((z (N + 1) - z N) - w) i ∈ Ideal.span {algebraMap R B π} ^ (N - c) := by
    intro N
    refine hc N (z (N + 1) - z N) ?_
    intro i
    have h1 : u i - φ (z (N + 1)) i ∈ Ideal.span {algebraMap R B π} ^ (N + 1) := by
      simpa using hz (N + 1) i
    have h2 : u i - φ (z N) i ∈ Ideal.span {algebraMap R B π} ^ N := by
      simpa using hz N i
    have h3 : Ideal.span {algebraMap R B π} ^ (N + 1) ≤ Ideal.span {algebraMap R B π} ^ N :=
      Ideal.pow_le_pow_right (Nat.le_succ N)
    have hcoord : φ (z (N + 1) - z N) i = φ (z (N + 1)) i - φ (z N) i := by
      rw [map_sub, Pi.sub_apply]
    rw [hcoord]
    have : φ (z (N + 1)) i - φ (z N) i = (u i - φ (z N) i) - (u i - φ (z (N + 1)) i) := by ring
    rw [this]
    exact Ideal.sub_mem _ h2 (h3 h1)
  choose w hwker hwdiff using hinc
  let z' : ℕ → (Fin t → B) :=
    fun N => z 0 + ∑ k ∈ Finset.range N, ((z (k + 1) - z k) - w k)
  have hz'_diff : ∀ N, z' (N + 1) - z' N = (z (N + 1) - z N) - w N := by
    intro N
    simp only [z', Finset.sum_range_succ]
    abel
  have hphi : ∀ N, φ (z' N) = φ (z N) := by
    intro N
    induction N with
    | zero => simp [z']
    | succ N ih =>
        have h1 : z' (N + 1) = z' N + ((z (N + 1) - z N) - w N) := by
          rw [show z' (N + 1) = z' N + (z' (N + 1) - z' N) from by abel, hz'_diff N]
        have h2 : φ ((z (N + 1) - z N) - w N) = φ (z (N + 1)) - φ (z N) := by
          rw [map_sub, map_sub, LinearMap.mem_ker.mp (hwker N), sub_zero]
        rw [h1, map_add, ih, h2]
        abel
  -- convergence of the corrected sequence
  obtain ⟨b, hb⟩ := Work.DSG4b.series_limit_of_pow_mem (A := B)
    (I := Ideal.span {algebraMap R B π}) (inferInstance) (fun _ : Fin t => c)
    (fun N i => (z' (N + 1) - z' N) i) (fun N i => by
      rw [hz'_diff N]
      exact hwdiff N i)
  let ζ : Fin t → B := z' 0 + b
  have hlim : ∀ N i, (z' N) i - ζ i ∈ Ideal.span {algebraMap R B π} ^ (N - c) := by
    intro N i
    have h := hb i N
    have hsum : (∑ k ∈ Finset.range N, ((z' (k + 1) - z' k) i)) = (z' N - z' 0) i := by
      have := congrArg (fun v : Fin t → B => v i) (Finset.sum_range_sub z' N)
      simpa using this
    rw [hsum] at h
    convert h using 1
    simp only [ζ, Pi.add_apply, Pi.sub_apply]
    ring
  -- `φ ζ = u` by Hausdorffness
  have key : ∀ M i, (φ ζ - u) i ∈ Ideal.span {algebraMap R B π} ^ M := by
    intro M i
    have h1 : ∀ j, (ζ - z' (M + c)) j ∈ Ideal.span {algebraMap R B π} ^ M := by
      intro j
      have h := hlim (M + c) j
      rw [Nat.add_sub_cancel] at h
      have : (ζ - z' (M + c)) j = -((z' (M + c)) j - ζ j) := by
        simp only [Pi.sub_apply]; ring
      rw [this]
      exact neg_mem h
    have h2 : (φ (ζ - z' (M + c))) i ∈ Ideal.span {algebraMap R B π} ^ M := by
      rw [apply_eq_sum_single_fin]
      exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (h1 j)
    have h4 : (φ (z' (M + c)) - u) i ∈ Ideal.span {algebraMap R B π} ^ M := by
      have hle : Ideal.span {algebraMap R B π} ^ (M + c) ≤ Ideal.span {algebraMap R B π} ^ M :=
        Ideal.pow_le_pow_right (Nat.le_add_right M c)
      have h := hle (by simpa using hz (M + c) i)
      have : (φ (z' (M + c)) - u) i = -(u i - φ (z (M + c)) i) := by
        rw [hphi (M + c)]
        simp only [Pi.sub_apply]; ring
      rw [this]
      exact neg_mem h
    have hsplit : φ ζ - u = φ (ζ - z' (M + c)) + (φ (z' (M + c)) - u) := by
      rw [map_sub]; abel
    rw [hsplit, Pi.add_apply]
    exact Ideal.add_mem _ h2 h4
  have hzero : φ ζ - u = 0 := by
    funext i
    exact IsHausdorff.haus' (I := Ideal.span {algebraMap R B π}) ((φ ζ - u) i)
      (fun M => SModEq.sub_mem.mpr (by simpa [Ideal.smul_eq_mul] using key M i))
  exact LinearMap.mem_range.mpr ⟨ζ, sub_eq_zero.mp hzero⟩

end Work.DSM2b
