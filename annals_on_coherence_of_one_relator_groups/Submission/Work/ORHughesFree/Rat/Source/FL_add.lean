import Mathlib
import Submission.Work.ORHughesFree.Rat.Source.Setup

namespace Work.ORHughesFree.Rat.Source

/-- **The sum case for the left family `Rat.FL`** (mirror of `Rat.Source.F_add`).

For `y, z ≠ 0` with least elements `Sy ∈ FL y`, `Sz ∈ FL z` and witnesses `φuy·y ∈ A Sy`,
`φuz·z ∈ A Sz`, one has

  `V ∈ FL (y+z) ↔ Sy ≤ V ∧ Sz ≤ V ∧ uy·uz⁻¹ ∈ V`.

Indeed `V ∈ FL w ↔ ∃ u, φu·w ∈ A V` (`Rat.mem_BL_iff_ofGroup_mul`); additive purity
(`Weak.A_add_left`) splits `φu·(y+z) = φu·y + φu·z`, and at a level `V ∈ FL y ∩ FL z` the left
translate sets `TL y V`, `TL z V` are the *right* cosets `V·uy`, `V·uz` (`TL_eq_coset`), whose
coincidence is exactly `uy·uz⁻¹ ∈ V`. -/
theorem FL_add {U : Type} [Group U] {y z : Work.ORHughesFree.RatU U} {Sy Sz : Subgroup U} {uy uz : U}
    (hy : y ≠ 0) (hz : z ≠ 0)
    (hSy : Work.ORHughesFree.Rat.IsLeastL y Sy)
    (hSz : Work.ORHughesFree.Rat.IsLeastL z Sz)
    (huy : Work.ORHughesFree.RatU.ofGroup uy * y ∈ Work.ORHughesFree.Rat.A Sy)
    (huz : Work.ORHughesFree.RatU.ofGroup uz * z ∈ Work.ORHughesFree.Rat.A Sz) :
    ∀ V : Subgroup U, V ∈ Work.ORHughesFree.Rat.FL (y + z) ↔
      Sy ≤ V ∧ Sz ≤ V ∧ uy * uz⁻¹ ∈ V := by
  intro V
  constructor
  · -- Forward: some left translate of `y+z` lies in `A V`; split it by additive purity.
    intro hV
    obtain ⟨u, hu⟩ := Rat.mem_BL_iff_ofGroup_mul.mp hV
    have hsplit : RatU.ofGroup u * (y + z) = RatU.ofGroup u * y + RatU.ofGroup u * z :=
      mul_add _ _ _
    have hu' : RatU.ofGroup u * y + RatU.ofGroup u * z ∈ Rat.A V := by
      rwa [hsplit] at hu
    have huy_mem : RatU.ofGroup u * y ∈ Rat.A V := Weak.A_add_left hu'
    have huz_mem : RatU.ofGroup u * z ∈ Rat.A V :=
      Weak.A_add_left (x := RatU.ofGroup u * z) (y := RatU.ofGroup u * y)
        (by rwa [add_comm] at hu')
    -- The two translate sets at `V` are the right cosets `V·uy` and `V·uz`.
    have hVy : V ∈ Rat.FL y := Rat.mem_BL_iff_ofGroup_mul.mpr ⟨u, huy_mem⟩
    have hVz : V ∈ Rat.FL z := Rat.mem_BL_iff_ofGroup_mul.mpr ⟨u, huz_mem⟩
    have hSyV : Sy ≤ V := hSy.le hVy
    have hSzV : Sz ≤ V := hSz.le hVz
    refine ⟨hSyV, hSzV, ?_⟩
    have huyS : RatU.ofGroup uy * y ∈ Rat.A V := Rat.A_mono hSyV huy
    have huzS : RatU.ofGroup uz * z ∈ Rat.A V := Rat.A_mono hSzV huz
    have hcy := TL_eq_coset hy hVy huyS
    have hcz := TL_eq_coset hz hVz huzS
    have hmy : u ∈ {u : U | RatU.ofGroup u * y ∈ Rat.A V} := huy_mem
    have hmz : u ∈ {u : U | RatU.ofGroup u * z ∈ Rat.A V} := huz_mem
    rw [hcy] at hmy
    rw [hcz] at hmz
    obtain ⟨v, hv, hvu⟩ := hmy
    obtain ⟨w, hw, hwu⟩ := hmz
    -- `v·uy = u = w·uz`, hence `uy·uz⁻¹ = v⁻¹·w ∈ V`.
    have heq : v * uy = w * uz := by rw [← hvu, ← hwu]
    have h1 : v * (uy * uz⁻¹) = w := by
      rw [← mul_assoc, heq, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : uy * uz⁻¹ = v⁻¹ * w := by
      rw [← h1]
      group
    rw [h2]
    exact V.mul_mem (V.inv_mem hv) hw
  · -- Backward: `φuy·y ∈ A V` and `φuy·z = φ(uy·uz⁻¹)·(φuz·z) ∈ A V`.
    rintro ⟨hSyV, hSzV, huyz⟩
    refine Rat.mem_BL_iff_ofGroup_mul.mpr ⟨uy, ?_⟩
    have hyA : RatU.ofGroup uy * y ∈ Rat.A V := Rat.A_mono hSyV huy
    have hzA : RatU.ofGroup uz * z ∈ Rat.A V := Rat.A_mono hSzV huz
    have hgA : RatU.ofGroup (uy * uz⁻¹) ∈ Rat.A V := Weak.A_ofGroup_mem huyz
    have hzV : RatU.ofGroup uy * z ∈ Rat.A V := by
      have h1 : RatU.ofGroup (uy * uz⁻¹) * (RatU.ofGroup uz * z) = RatU.ofGroup uy * z := by
        rw [← mul_assoc, ← RatU.ofGroup_mul, show uy * uz⁻¹ * uz = uy by group]
      rw [← h1]
      exact (Weak.ASub V).mul_mem hgA hzA
    rw [mul_add]
    exact (Weak.ASub V).add_mem hyA hzV

end Work.ORHughesFree.Rat.Source
