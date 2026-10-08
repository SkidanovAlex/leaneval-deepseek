import Mathlib
import Submission.Work.Hering.Config
import Submission.Work.Hering.HardCore.aut_inv_conj_V

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.Hering.HardCore

/-- **Adjustment of a witness.**  In the reduced configuration, suppose `y ∉ C = C_G(V)` has
`y² ∈ C`, and suppose some `x ∉ C` has `x² ∈ V#{1}`.  Then `y` can be adjusted by an element
`c ∈ C` so that `(y c)² ∈ V` is a non-identity involution.

The proof: the conjugation action of `y` (resp. `x`) on `V` is a non-trivial involution of
`Aut(V)` (`y²`, `x²` lie in `C`, and `V` has exponent two so `V ≤ C`); by
`aut_inv_conj_V` any two such are conjugate, so `conj_g ∘ conj_y ∘ conj_g⁻¹ = conj_x` for the
`g` realising that automorphism (`hAut`).  Hence `w := g y g⁻¹ x⁻¹ ∈ C`, and
`c := g⁻¹ (x⁻¹ w⁻¹ x) g` satisfies `y c = g⁻¹ x g`, whose square is the non-identity element
`g⁻¹ x² g` of `V`. -/
theorem adjust_witness {G : Type*} [Group G] [Finite G] (V C : Subgroup G) (hV : V.Normal)
    (hcard : Nat.card V = 8) (hexp : ∀ x ∈ V, x * x = 1)
    (hC : C = Subgroup.centralizer ((V : Set G))) (hAut : ActsAsAut V hV)
    (hwit : ∃ x : G, x ∉ C ∧ x * x ∈ V ∧ x * x ≠ 1)
    {y : G} (hyC : y ∉ C) (hy2 : y * y ∈ C) :
    ∃ c ∈ C, (y * c) * (y * c) ∈ V ∧ (y * c) * (y * c) ≠ 1 := by
  obtain ⟨x, hxC, hx2V, hx2ne⟩ := hwit
  haveI : V.Normal := hV
  -- `C = C_G(V)` is normal.
  have hCn : C.Normal := by rw [hC]; exact Subgroup.normal_centralizer
  -- `V` has exponent two, hence is abelian, hence `V ≤ C_G(V) = C`.
  have hVC : V ≤ C := by
    rw [hC]
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hv2 : v * v = 1 := hexp v hv
    have hw2 : w * w = 1 := hexp w hw
    have hvw : (v * w) * (v * w) = 1 := hexp (v * w) (V.mul_mem hv hw)
    have h1 : v⁻¹ = v := inv_eq_of_mul_eq_one_left hv2
    have h2 : w⁻¹ = w := inv_eq_of_mul_eq_one_left hw2
    have h3 : v * w = (v * w)⁻¹ := (mul_eq_one_iff_eq_inv).mp hvw
    have hcomm : v * w = w * v := by rw [h3, mul_inv_rev, h2, h1]
    exact hcomm.symm
  -- An element of `C` acts trivially by conjugation on `V`.
  have hconj_one : ∀ z : G, z ∈ C → MulAut.conjNormal (H := V) z = 1 := by
    intro z hz
    have hz' : z ∈ Subgroup.centralizer (V : Set G) := hC ▸ hz
    ext w
    rw [MulAut.conjNormal_apply, MulAut.one_apply]
    have hzw : z * (w : G) = (w : G) * z := ((Subgroup.mem_centralizer_iff).mp hz' w w.2).symm
    rw [hzw, mul_assoc, mul_inv_cancel, mul_one]
  -- Conversely, an element acting trivially by conjugation lies in `C`.
  have hmemC : ∀ z : G, MulAut.conjNormal (H := V) z = 1 → z ∈ C := by
    intro z hz
    rw [hC, Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : (MulAut.conjNormal (H := V) z) ⟨w, hw⟩ = ⟨w, hw⟩ := by rw [hz, MulAut.one_apply]
    have h2 : z * w * z⁻¹ = w := congrArg Subtype.val h1
    have h4 : z * w = w * z := by
      calc z * w = (z * w * z⁻¹) * z := by group
        _ = w * z := by rw [h2]
    exact h4.symm
  have hx2C : x * x ∈ C := hVC hx2V
  have hα_ne : MulAut.conjNormal (H := V) y ≠ 1 := fun h => hyC (hmemC y h)
  have hβ_ne : MulAut.conjNormal (H := V) x ≠ 1 := fun h => hxC (hmemC x h)
  have hα2 : MulAut.conjNormal (H := V) y * MulAut.conjNormal (H := V) y = 1 := by
    rw [← map_mul]; exact hconj_one (y*y) hy2
  have hβ2 : MulAut.conjNormal (H := V) x * MulAut.conjNormal (H := V) x = 1 := by
    rw [← map_mul]; exact hconj_one (x*x) hx2C
  have hexp' : ∀ z : ↥V, z * z = 1 := fun z => Subtype.ext (by simpa using hexp z z.2)
  -- The two involutions of `Aut(V)` are conjugate.
  obtain ⟨φ, hφ⟩ := Work.Hering.HardCore.aut_inv_conj_V hcard hexp'
      (MulAut.conjNormal (H := V) y) (MulAut.conjNormal (H := V) x) hα_ne hα2 hβ_ne hβ2
  -- Realise `φ` by an element `g` of `G`.
  obtain ⟨g, hg⟩ := hAut φ
  have hφconj : φ = MulAut.conjNormal (H := V) g := by
    ext w
    rw [MulAut.conjNormal_apply]
    simpa using congrArg Subtype.val (hg w)
  have hΦ : MulAut.conjNormal (H := V) (g * y * g⁻¹) = MulAut.conjNormal (H := V) x := by
    rw [map_mul, map_mul, map_inv, hφconj.symm]
    exact hφ.symm
  have hwC : (g * y * g⁻¹) * x⁻¹ ∈ C := by
    apply hmemC
    rw [map_mul, hΦ, map_inv, mul_inv_cancel]
  refine ⟨g⁻¹ * (x⁻¹ * (((g * y * g⁻¹) * x⁻¹))⁻¹ * x) * g, ?_, ?_, ?_⟩
  · have hxw : x⁻¹ * (((g * y * g⁻¹) * x⁻¹))⁻¹ * x ∈ C := by
      simpa using hCn.conj_mem (((g * y * g⁻¹) * x⁻¹))⁻¹ (C.inv_mem hwC) x⁻¹
    simpa using hCn.conj_mem (x⁻¹ * (((g * y * g⁻¹) * x⁻¹))⁻¹ * x) hxw g⁻¹
  · have hyc : y * (g⁻¹ * (x⁻¹ * (((g * y * g⁻¹) * x⁻¹))⁻¹ * x) * g) = g⁻¹ * x * g := by group
    rw [hyc]
    have he : (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
    rw [he]
    simpa using hV.conj_mem (x * x) hx2V g⁻¹
  · intro h1
    have hyc : y * (g⁻¹ * (x⁻¹ * (((g * y * g⁻¹) * x⁻¹))⁻¹ * x) * g) = g⁻¹ * x * g := by group
    rw [hyc] at h1
    have he : (g⁻¹ * x * g) * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
    rw [he] at h1
    apply hx2ne
    have hh : g * (g⁻¹ * (x * x) * g) * g⁻¹ = 1 := by rw [h1]; group
    rw [← hh]; group

end Work.Hering.HardCore
