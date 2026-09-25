import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.KummerExtension

/-- If `k` contains a primitive `n`-th root of unity `ζ` and `M` is a `k`-algebra
(a field), then every `n`-th root of unity in `M` is the image under `algebraMap k M`
of an `n`-th root of unity of `k`.

This is the statement that the `n`-th roots of unity of `M` lie in the image of
those of `k`, which holds because `X ^ n - 1` splits over `k` into linear factors
`∏_{i < n} (X - ζ ^ i)` and the algebra map is injective. -/
theorem rootsOfUnity_mem_map_of_isPrimitiveRoot
    {k M : Type*} [Field k] [Field M] [Algebra k M] (n : ℕ) [NeZero n]
    {ζ : k} (hζ : IsPrimitiveRoot ζ n) (η : Mˣ) (hη : η ∈ rootsOfUnity n M) :
    ∃ η₀ : rootsOfUnity n k, Units.map (algebraMap k M : k →* M) (η₀ : kˣ) = η := by
  -- `algebraMap k M` is injective, so it carries primitive roots to primitive roots.
  have hf : Function.Injective (algebraMap k M : k →* M) :=
    FaithfulSMul.algebraMap_injective k M
  -- Hence it maps the `n`-th roots of unity of `k` onto those of `M`.
  have hmap := hζ.map_rootsOfUnity (f := (algebraMap k M : k →* M)) hf
  rw [← hmap] at hη
  obtain ⟨x, hx, heq⟩ := Subgroup.mem_map.mp hη
  exact ⟨⟨x, hx⟩, heq⟩

end Commons.FieldTheory.KummerExtension