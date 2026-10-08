import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

lemma c_cubed {M : Type*} [Group M] (u v c : M)
    (hu : u ^ 3 = 1) (huv : u * v = c * (v * u)) (hcu : Commute c u) :
    c ^ 3 = 1 := by
  -- Conjugation by `u` sends `v` to `c * v` ...
  have h1 : u * v * u⁻¹ = c * v := by
    calc u * v * u⁻¹ = (c * (v * u)) * u⁻¹ := by rw [huv]
      _ = c * v := by group
  -- ... and fixes `c`, since `c` commutes with `u`.
  have hcu' : u * c * u⁻¹ = c := by
    rw [← hcu.eq]; group
  have hcu'' : u * (c * c) * u⁻¹ = c * c := by
    calc u * (c * c) * u⁻¹ = (u * c * u⁻¹) * (u * c * u⁻¹) := by group
      _ = c * c := by rw [hcu']
  -- So conjugation by `u` acts on `v` as left multiplication by `c`
  -- and on `c` trivially; iterating three times multiplies `v` by `c^3` ...
  have h2 : u * (c * v) * u⁻¹ = (c * c) * v := by
    calc u * (c * v) * u⁻¹ = (u * c * u⁻¹) * (u * v * u⁻¹) := by group
      _ = c * (c * v) := by rw [hcu', h1]
      _ = (c * c) * v := by rw [mul_assoc]
  have h3 : u * ((c * c) * v) * u⁻¹ = (c * (c * c)) * v := by
    calc u * ((c * c) * v) * u⁻¹ = (u * (c * c) * u⁻¹) * (u * v * u⁻¹) := by group
      _ = (c * c) * (c * v) := by rw [hcu'', h1]
      _ = (c * (c * c)) * v := by group
  have hchain : (c * (c * c)) * v = v := by
    calc (c * (c * c)) * v = u * ((c * c) * v) * u⁻¹ := h3.symm
      _ = u * (u * (c * v) * u⁻¹) * u⁻¹ := by rw [← h2]
      _ = u * (u * (u * v * u⁻¹) * u⁻¹) * u⁻¹ := by rw [← h1]
      _ = (u * u * u) * v * (u⁻¹ * u⁻¹ * u⁻¹) := by group
      _ = v := by
        rw [show u * u * u = 1 by rw [mul_assoc, ← pow_three, hu],
            show u⁻¹ * u⁻¹ * u⁻¹ = 1 by
              rw [mul_assoc, ← pow_three, inv_pow, hu, inv_one]]
        group
  -- ... but conjugation by `u^3 = 1` is the identity, so `c^3 * v = v`, i.e. `c^3 = 1`.
  have hcv : c ^ 3 * v = v := by rw [pow_three]; exact hchain
  exact mul_right_cancel (by rw [hcv, one_mul])

end Work.ThmF.ChV3.Prove
