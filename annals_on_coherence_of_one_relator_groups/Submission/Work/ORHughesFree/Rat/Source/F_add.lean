import Mathlib
import Submission.Work.ORHughesFree.Rat.Source.Setup

namespace Work.ORHughesFree.Rat.Source

open Work.ORHughesFree

/-- **The sum case for `Rat.F`.**  If `Sy` (resp. `Sz`) is the least element of `Rat.F y` (resp.
`Rat.F z`) and `y·φuy ∈ Rat.A Sy`, `z·φuz ∈ Rat.A Sz`, then for every subgroup `V`

`V ∈ Rat.F (y + z) ↔ Sy ≤ V ∧ Sz ≤ V ∧ uy⁻¹ * uz ∈ V`.

The forward implication is the translate dichotomy `Rat.Dich.both_of_ne_zero` applied to the two
non-zero elements `y·φuy` and `z·φuz` at the level `V`: a common translate `u` of `y` and `z` at
`V` forces `uy⁻¹u ∈ V` and `uz⁻¹u ∈ V`.  Conversely, if `Sy, Sz ≤ V` and `uy⁻¹uz ∈ V`, then the
translate `uz` works for both `y` and `z`. -/
theorem F_add {U : Type} [Group U] {y z : Work.ORHughesFree.RatU U} {Sy Sz : Subgroup U} {uy uz : U}
    (hy : y ≠ 0) (hz : z ≠ 0)
    (hSy : Work.ORHughesFree.Rat.IsLeastF y Sy)
    (hSz : Work.ORHughesFree.Rat.IsLeastF z Sz)
    (huy : y * Work.ORHughesFree.RatU.ofGroup uy ∈ Work.ORHughesFree.Rat.A Sy)
    (huz : z * Work.ORHughesFree.RatU.ofGroup uz ∈ Work.ORHughesFree.Rat.A Sz) :
    ∀ V : Subgroup U, V ∈ Work.ORHughesFree.Rat.F (y + z) ↔
      Sy ≤ V ∧ Sz ≤ V ∧ uy⁻¹ * uz ∈ V := by
  intro V
  constructor
  · intro hV
    -- A common translate `u` of `y` and `z` at level `V`.
    obtain ⟨u, hyu, hzu⟩ := (Work.ORHughesFree.Rat.mem_F_add_iff y z V).mp hV
    have hVy : V ∈ Work.ORHughesFree.Rat.F y :=
      (Work.ORHughesFree.Rat.mem_F_iff' y V).mpr ⟨u, hyu⟩
    have hVz : V ∈ Work.ORHughesFree.Rat.F z :=
      (Work.ORHughesFree.Rat.mem_F_iff' z V).mpr ⟨u, hzu⟩
    have hSyV : Sy ≤ V := hSy.le hVy
    have hSzV : Sz ≤ V := hSz.le hVz
    -- The tails of `y` and `z` lie in `Rat.A V`.
    have huyV : y * Work.ORHughesFree.RatU.ofGroup uy ∈ Work.ORHughesFree.Rat.A V :=
      Work.ORHughesFree.Rat.A_mono hSyV huy
    have huzV : z * Work.ORHughesFree.RatU.ofGroup uz ∈ Work.ORHughesFree.Rat.A V :=
      Work.ORHughesFree.Rat.A_mono hSzV huz
    -- The translate dichotomy applied to `y·φuy` and to `z·φuz`.
    have hy0 : y * Work.ORHughesFree.RatU.ofGroup uy ≠ 0 :=
      mul_ofGroup_ne_zero hy uy
    have hz0 : z * Work.ORHughesFree.RatU.ofGroup uz ≠ 0 :=
      mul_ofGroup_ne_zero hz uz
    have huyu : uy⁻¹ * u ∈ V := by
      have h1 : Work.ORHughesFree.RatU.ofGroup u
          = Work.ORHughesFree.RatU.ofGroup uy *
            Work.ORHughesFree.RatU.ofGroup (uy⁻¹ * u) := by
        rw [← Work.ORHughesFree.RatU.ofGroup_mul, mul_inv_cancel_left]
      have hkey : (y * Work.ORHughesFree.RatU.ofGroup uy) *
            Work.ORHughesFree.RatU.ofGroup (uy⁻¹ * u)
          = y * Work.ORHughesFree.RatU.ofGroup u := by
        rw [mul_assoc, ← h1]
      exact (Work.ORHughesFree.Rat.Dich.both_of_ne_zero
        (y * Work.ORHughesFree.RatU.ofGroup uy) hy0).1 V (uy⁻¹ * u) huyV
        (by rw [hkey]; exact hyu)
    have huzu : uz⁻¹ * u ∈ V := by
      have h1 : Work.ORHughesFree.RatU.ofGroup u
          = Work.ORHughesFree.RatU.ofGroup uz *
            Work.ORHughesFree.RatU.ofGroup (uz⁻¹ * u) := by
        rw [← Work.ORHughesFree.RatU.ofGroup_mul, mul_inv_cancel_left]
      have hkey : (z * Work.ORHughesFree.RatU.ofGroup uz) *
            Work.ORHughesFree.RatU.ofGroup (uz⁻¹ * u)
          = z * Work.ORHughesFree.RatU.ofGroup u := by
        rw [mul_assoc, ← h1]
      exact (Work.ORHughesFree.Rat.Dich.both_of_ne_zero
        (z * Work.ORHughesFree.RatU.ofGroup uz) hz0).1 V (uz⁻¹ * u) huzV
        (by rw [hkey]; exact hzu)
    refine ⟨hSyV, hSzV, ?_⟩
    have hsplit : uy⁻¹ * uz = (uy⁻¹ * u) * (uz⁻¹ * u)⁻¹ := by group
    rw [hsplit]
    exact V.mul_mem huyu (V.inv_mem huzu)
  · rintro ⟨hSyV, hSzV, hwV⟩
    -- The common translate `uz` witnesses `V ∈ Rat.F (y + z)`.
    refine (Work.ORHughesFree.Rat.mem_F_add_iff y z V).mpr ⟨uz, ?_, ?_⟩
    · have h1 : Work.ORHughesFree.RatU.ofGroup uz
          = Work.ORHughesFree.RatU.ofGroup uy *
            Work.ORHughesFree.RatU.ofGroup (uy⁻¹ * uz) := by
        rw [← Work.ORHughesFree.RatU.ofGroup_mul, mul_inv_cancel_left]
      have hkey : y * Work.ORHughesFree.RatU.ofGroup uz
          = (y * Work.ORHughesFree.RatU.ofGroup uy) *
            Work.ORHughesFree.RatU.ofGroup (uy⁻¹ * uz) := by
        rw [h1, mul_assoc]
      rw [hkey]
      exact (Work.ORHughesFree.Rat.Weak.ASub V).mul_mem
        (Work.ORHughesFree.Rat.A_mono hSyV huy)
        (Work.ORHughesFree.Rat.Weak.A_ofGroup_mem hwV)
    · exact Work.ORHughesFree.Rat.A_mono hSzV huz

end Work.ORHughesFree.Rat.Source
