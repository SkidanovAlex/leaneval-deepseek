import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Eigenvector

/-- Helper: an ordered product of endomorphisms applied to a vector `x` on which each factor acts
as the scalar `a i` equals the product of the scalars times `x`. -/
private lemma list_prod_apply_of_forall_apply_eq_smul {K M ι : Type*} [Field K] [AddCommMonoid M]
    [Module K M] (g : ι → Module.End K M) (x : M) (l : List ι) (a : ι → K)
    (h : ∀ i ∈ l, g i x = a i • x) :
    (l.map g).prod x = (l.map a).prod • x := by
  induction l with
  | nil => simp
  | cons i t ih =>
      have hii : g i x = a i • x := h i List.mem_cons_self
      have ht : ∀ j ∈ t, g j x = a j • x := fun j hj => h j (List.mem_cons_of_mem i hj)
      rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, Module.End.mul_apply,
        ih ht, LinearMap.map_smul, hii, smul_smul, mul_comm (t.map a).prod (a i)]

/-- Simultaneous eigenvectors of a family of linear operators over a field, with pairwise
separating eigenvalue functions `ν i : κ → K`, are linearly independent.

(Note: the field hypothesis and `x i ≠ 0` are both necessary; over a general commutative ring the
sharp conclusion is only `∀ i, c i • x i = 0`, and a zero eigenvector can carry arbitrary
coefficients.)

Suggested proof (interpolation): for a fixed `i₀`, choose for every `i ≠ i₀` an index `k i` with
`ν i (k i) ≠ ν i₀ (k i)` and consider the operator
`∏ i ∈ univ.erase i₀, (T (k i) - ν i (k i) • 1)` (a product in `Module.End K M`).  Each factor maps
the eigenspace of `ν i₀` into itself and kills `x i`; the product kills every `x i` with `i ≠ i₀`
and sends `x i₀` to `(∏ i ≠ i₀, (ν i₀ (k i) - ν i (k i))) • x i₀`, whose scalar is non-zero.  Apply
it to `∑ i, c i • x i = 0` (induct over `Finset.univ.erase i₀` to relate the product of operators
to the product of scalars on an eigenvector) to get `c i₀ • x i₀ = 0`, hence `c i₀ = 0` using
`hx i₀` and the field structure. -/
theorem linearIndependent_of_separating_eigenvalues {K M ι κ : Type*} [Field K] [AddCommGroup M]
    [Module K M] [Fintype ι] [DecidableEq ι] (T : κ → Module.End K M) (x : ι → M)
    (hx : ∀ i, x i ≠ 0) (ν : ι → κ → K) (heig : ∀ i k, T k (x i) = ν i k • x i)
    (hsep : ∀ i i', i ≠ i' → ∃ k, ν i k ≠ ν i' k) (c : ι → K)
    (hsum : ∑ i, c i • x i = 0) : ∀ i, c i = 0 := by
  classical
  intro i₀
  set s : Finset ι := Finset.univ.erase i₀ with hs
  have hmem_s : ∀ i, i ∈ s ↔ i ≠ i₀ := by
    intro i
    rw [hs]
    simp [Finset.mem_erase]
  let kf : {i // i ∈ s} → κ :=
    fun i => Classical.choose (hsep i.1 i₀ ((hmem_s i.1).mp i.2))
  have hkf : ∀ i : {i // i ∈ s}, ν i.1 (kf i) ≠ ν i₀ (kf i) :=
    fun i => Classical.choose_spec (hsep i.1 i₀ ((hmem_s i.1).mp i.2))
  let g : {i // i ∈ s} → Module.End K M := fun i => T (kf i) - ν i.1 (kf i) • 1
  let l : List {i // i ∈ s} := s.attach.toList
  have hl : l = s.attach.toList := rfl
  have hproprep : ∀ (i : ι), (l.map g).prod (x i) =
      (l.map (fun j => ν i (kf j) - ν j.1 (kf j))).prod • x i := by
    intro i
    apply list_prod_apply_of_forall_apply_eq_smul
    intro j hj
    show (T (kf j) - ν j.1 (kf j) • 1) (x i) = (ν i (kf j) - ν j.1 (kf j)) • x i
    rw [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, heig i (kf j),
      ← sub_smul]
  have hPxi : ∀ i, i ≠ i₀ → (l.map g).prod (x i) = 0 := by
    intro i hi
    rw [hproprep i]
    have hmem : i ∈ s := (hmem_s i).mpr hi
    have hz : (l.map (fun j => ν i (kf j) - ν j.1 (kf j))).prod = 0 := by
      rw [List.prod_eq_zero_iff]
      refine List.mem_map.mpr ⟨⟨i, hmem⟩, ?_, ?_⟩
      · rw [hl, Finset.mem_toList]
        exact Finset.mem_attach s ⟨i, hmem⟩
      · simp
    rw [hz, zero_smul]
  have hPxi₀ : (l.map g).prod (x i₀) =
      (l.map (fun j => ν i₀ (kf j) - ν j.1 (kf j))).prod • x i₀ := hproprep i₀
  have hne : (l.map (fun j => ν i₀ (kf j) - ν j.1 (kf j))).prod ≠ 0 := by
    intro h0
    rw [List.prod_eq_zero_iff] at h0
    rcases List.mem_map.mp h0 with ⟨j, hj, hj0⟩
    have hjnz : ν i₀ (kf j) - ν j.1 (kf j) ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hkf j))
    exact hjnz hj0
  have hsq : (l.map g).prod (∑ i, c i • x i) = 0 := by rw [hsum, map_zero]
  have hsum' : (l.map g).prod (∑ i, c i • x i) = c i₀ • (l.map g).prod (x i₀) := by
    rw [map_sum]
    have h1 : ∀ b ∈ (Finset.univ : Finset ι), b ≠ i₀ →
        (l.map g).prod (c b • x b) = 0 := by
      intro b _ hb
      rw [map_smul, hPxi b hb, smul_zero]
    have h2 : i₀ ∉ (Finset.univ : Finset ι) → (l.map g).prod (c i₀ • x i₀) = 0 :=
      fun h => absurd (Finset.mem_univ i₀) h
    rw [Finset.sum_eq_single i₀ h1 h2, map_smul]
  have hkey : c i₀ • (l.map g).prod (x i₀) = 0 := by rw [← hsum', hsq]
  rw [hPxi₀, smul_smul] at hkey
  have hcs : c i₀ * (l.map (fun j => ν i₀ (kf j) - ν j.1 (kf j))).prod = 0 :=
    (smul_eq_zero.mp hkey).resolve_right (hx i₀)
  exact (mul_eq_zero.mp hcs).resolve_right hne

end Commons.LinearAlgebra.Eigenvector