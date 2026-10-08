/-
# The centre of `SZ E` is `Q₀ = {(0,y)}`

Peterfalvi II, Ch. VI §3: `Q₀ = {(0,y)}` is the centre of the case-c Suzuki group `Q = SZ E`
(it is also `Ω₁(Q) = Q'`).  The two hypotheses are exactly what the argument needs:

* `hσ : ∃ x, σE x ≠ x` (the involution is not the identity);
* `hTr : ∀ c, σE c = c → ∃ y, y + σE y = c` (the trace `y ↦ y + σE y` is onto the fixed
  field, i.e. `E/F` is Galois of degree 2) — this is what lets one test centrality against an
  element with an arbitrary `x`-coordinate.

Both hold for `E n = GaloisField 2 (2n)` with `n ≥ 1`.  Counterexample to the `hσ`-only version:
`σ = id` makes `SZ E` abelian.  (`Submission/Work/PSU3/Notes.md` §3.)
-/
import Submission.Work.PSU3.FMap

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

namespace Work.PSU3

variable {E : Type*} [Field E] [FrobeniusInvolution E]

/-- **The centre of `SZ E`.**  `p` is central iff `p.x = 0`, i.e. `p ∈ Q₀`. -/
theorem mem_center_iff (hσ : ∃ x : E, σE x ≠ x)
    (hTr : ∀ c : E, σE c = c → ∃ y : E, y + σE y = c) (p : SZ E) :
    p ∈ Subgroup.center (SZ E) ↔ p ∈ SZ.Q0 := by
  constructor
  · intro hp
    rw [SZ.mem_Q0_iff]
    by_contra hx
    have hcent : ∀ q : SZ E, q * p = p * q := Subgroup.mem_center_iff.mp hp
    have key : ∀ u : E, p.x * σE u = u * σE p.x := by
      intro u
      have hc : σE (u * σE u) = u * σE u := by rw [map_mul, σE_σE, mul_comm]
      obtain ⟨y, hy⟩ := hTr (u * σE u) hc
      have h1 := congrArg (fun z : SZ E => z.y) (hcent ⟨u, y, hy⟩)
      simp only [SZ.mul_y] at h1
      rw [add_comm y p.y] at h1
      exact add_left_cancel h1.symm
    have hσx : σE p.x = p.x := by
      have h1 := key 1
      simpa using h1.symm
    have hfix : ∀ u : E, σE u = u := by
      intro u
      have hpx : p.x ≠ 0 := by simpa [SZ.mem_Q0_iff] using hx
      have h2 := key u
      rw [hσx, mul_comm u p.x] at h2
      exact mul_left_cancel₀ hpx h2
    obtain ⟨u₀, hu₀⟩ := hσ
    exact hu₀ (hfix u₀)
  · intro hp
    rw [Subgroup.mem_center_iff]
    intro q
    rw [SZ.mem_Q0_iff] at hp
    ext
    · simp [hp]
    · simp only [SZ.mul_y, hp, map_zero, zero_mul, add_zero]
      ring

end Work.PSU3
