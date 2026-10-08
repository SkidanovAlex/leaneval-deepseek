import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- Pure field identity underlying `tilde_tilde_center_zs`.  With `W = c₀/v + c₀/u` (all the
divisions are by the non-zero elements `c₀, u, v`), one has `W ≠ 0` (because `W = c₀(u+v)/(uv)`
and `u ≠ v` in characteristic two gives `u + v ≠ 0`), `W/(c₀/v²) = v + v²/u` and
`u/((c₀/v²)·(c₀/W²)) = (u+v)²/u`.  (`c₀` cancels in both identities.) -/
theorem ttc_field_arith {m : ℕ} {u v c₀ : GaloisField 2 m}
    (hc₀ : c₀ ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    c₀ / v + c₀ / u ≠ 0 ∧
      (c₀ / v + c₀ / u) / (c₀ / v ^ 2) = v + v ^ 2 / u ∧
      u / ((c₀ / v ^ 2) * (c₀ / (c₀ / v + c₀ / u) ^ 2)) = (u + v) ^ 2 / u := by
  -- In characteristic two, `u ≠ v` gives `u + v ≠ 0`.
  have huv0 : u + v ≠ 0 := fun h => huv (CharTwo.add_eq_zero.mp h)
  -- `W = c₀/v + c₀/u = c₀(u+v)/(uv) ≠ 0`.
  have hW : c₀ / v + c₀ / u ≠ 0 := by
    intro h
    have hmul : (c₀ / v + c₀ / u) * (v * u) = 0 := by rw [h, zero_mul]
    field_simp at hmul
    exact mul_ne_zero hc₀ huv0 hmul
  refine ⟨hW, ?_, ?_⟩
  · field_simp
  · field_simp

end Work.ZassenhausSuzuki
