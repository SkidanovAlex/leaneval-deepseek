import Mathlib
import Submission.Work.DSEQP.Basic

/-!
# Common denominators for `A`-linear maps into the fraction ring `Frac A`

If `K` is the fraction ring of a domain `A` (i.e. `IsLocalization (nonZeroDivisors A) K`)
and `M` is a finite `A`-module, then any `A`-linear map `g : M →ₗ[A] K` has a *common
denominator*: there is `d ∈ nonZeroDivisors A` such that `d • g m` lies in the image of
`algebraMap A K` for every `m : M`.

The proof is the usual one. Every element of `K` can be written as `algebraMap a / algebraMap s`
with `s ∈ nonZeroDivisors A` (`IsLocalization.surj`); this is `exists_smul_eq_algebraMap`.
Taking it over a finite set of elements and multiplying the denominators gives a denominator
valid for the whole set (`exists_common_den`). Since `M` is finite, we may pick finitely many
generators `s i` of `M`; multiplying the denominators of the `g (s i)` produces a single `d`
that clears the denominator of `g m` for every `m` in the span of the generators, i.e. for
every `m : M`.
-/

namespace Work.DSEQP

/-- **Single denominator.**  Every element `x` of `K = Frac A` admits `d ∈ nonZeroDivisors A`
with `d • x` in the image of `algebraMap A K`; `d` is the denominator of `x`. -/
lemma exists_smul_eq_algebraMap (A K : Type*) [CommRing A] [IsDomain A] [CommRing K]
    [Algebra A K] [IsLocalization (nonZeroDivisors A) K] (x : K) :
    ∃ d ∈ nonZeroDivisors A, ∃ a : A, algebraMap A K a = d • x := by
  obtain ⟨⟨a, d⟩, hd⟩ := IsLocalization.surj (nonZeroDivisors A) x
  exact ⟨(d : A), d.2, a, by rw [Algebra.smul_def, mul_comm]; simpa using hd.symm⟩

/-- **Common denominator of a finite set.**  If every `x ∈ t` has a denominator in
`nonZeroDivisors A`, then a single `d ∈ nonZeroDivisors A` clears the denominators of all of
`t` at once. -/
lemma exists_common_den (A K : Type*) [CommRing A] [IsDomain A] [CommRing K]
    [Algebra A K] [IsLocalization (nonZeroDivisors A) K] (t : Finset K)
    (h : ∀ x ∈ t, ∃ d ∈ nonZeroDivisors A, ∃ a : A, algebraMap A K a = d • x) :
    ∃ d ∈ nonZeroDivisors A, ∀ x ∈ t, ∃ a : A, algebraMap A K a = d • x := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_mem _, fun x hx => by simp at hx⟩
  | insert x t hx ih =>
    obtain ⟨dx, hdx, ax, hax⟩ := h x (Finset.mem_insert_self x t)
    obtain ⟨D, hD, hD'⟩ := ih (fun y hy => h y (Finset.mem_insert_of_mem hy))
    refine ⟨D * dx, Submonoid.mul_mem _ hD hdx, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨D * ax, by rw [mul_smul, ← hax, Algebra.smul_def, ← map_mul]⟩
    · obtain ⟨ay, hay⟩ := hD' y hy
      exact ⟨dx * ay, by rw [mul_comm D dx, mul_smul, ← hay, Algebra.smul_def, ← map_mul]⟩

theorem exists_smul_mem_range_algebraMap (A K M : Type*) [CommRing A] [IsDomain A]
    [CommRing K] [Algebra A K] [IsLocalization (nonZeroDivisors A) K]
    [AddCommMonoid M] [Module A M] [Module.Finite A M] (g : M →ₗ[A] K) :
    ∃ d ∈ nonZeroDivisors A, ∀ m : M, ∃ a : A, algebraMap A K a = d • g m := by
  classical
  -- Finitely many generators of `M`.
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  -- A denominator for each generator.
  have hgen : ∀ i : Fin n, ∃ d ∈ nonZeroDivisors A, ∃ a : A, algebraMap A K a = d • g (s i) :=
    fun i => exists_smul_eq_algebraMap A K (g (s i))
  choose d hdmem a ha using hgen
  -- A single denominator for the images of all generators.
  have hden : ∀ x ∈ (Finset.univ.image fun i : Fin n => g (s i)),
      ∃ dd ∈ nonZeroDivisors A, ∃ aa : A, algebraMap A K aa = dd • x := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨d i, hdmem i, a i, ha i⟩
  obtain ⟨D, hD, hDkey⟩ := exists_common_den A K _ hden
  refine ⟨D, hD, fun m => ?_⟩
  -- Scalar multiplication by `D` sends the whole span of the generators into the image of
  -- `algebraMap`.
  have key : ∀ y ∈ Submodule.span A (Set.range s),
      D • g y ∈ (Algebra.linearMap A K).range := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        obtain ⟨az, haz⟩ := hDkey (g (s i)) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
        exact ⟨az, haz⟩
    | zero => rw [map_zero, smul_zero]; exact Submodule.zero_mem _
    | add u v hu hv ihu ihv => rw [map_add, smul_add]; exact Submodule.add_mem _ ihu ihv
    | smul c u hu ihu =>
        rw [map_smul, ← mul_smul, mul_comm, mul_smul]; exact Submodule.smul_mem _ c ihu
  have hm : m ∈ Submodule.span A (Set.range s) := by rw [hs]; exact Submodule.mem_top
  obtain ⟨az, haz⟩ := key m hm
  exact ⟨az, haz⟩

end Work.DSEQP
