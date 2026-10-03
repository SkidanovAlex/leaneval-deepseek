/-
# `gaussUnits`: the Gaussian unit group in coordinates (§16 model)

The §16 model represents `ℤ[i]/n` by coordinates `(r,s) ∈ (ZMod n)²` with the Gaussian product

  `gaussMul (r,s) (u,v) = (ru - sv, rv + su)`,

whose norm `gaussNorm (r,s) = r² + s²` is multiplicative (`gaussNorm_gaussMul`).  By
`Work.FIArea7.gaussMod_exists_inv_iff`, `(r,s)` is invertible for `gaussMul` exactly when
`gaussNorm (r,s)` is a unit of `ZMod n` — i.e. the group of units of `ℤ[i]/n` is

  `{p : (ZMod n)² // IsUnit (gaussNorm p)}`

with product `gaussMul`, identity `(1,0)` and inverse `(r,s)⁻¹ = (r t, −s t)`, `t = (r²+s²)⁻¹`
(`gaussMul_inv_cancel`).  This file records the definition layer and the laws that are pure ring
identities; the `CommGroup` instance on the subtype and the equivalence
`≃* (ZMod q)ˣ × (ZMod q)ˣ` for odd split `q` (via `omegaModel`) are the next links, and for
`q = 4d` the ramified prime `1+i` is handled separately — that is where Φ(4d)'s extra factor `2`
over `φ(4d)²` lives.
-/
import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7

/-- **The Gaussian product in coordinates**: `(r,s)(u,v) = (ru - sv, rv + su)`. -/
def gaussMul {n : ℕ} (p q : ZMod n × ZMod n) : ZMod n × ZMod n :=
  (p.1 * q.1 - p.2 * q.2, p.1 * q.2 + p.2 * q.1)

/-- **The Gaussian norm in coordinates**: `|(r,s)|² = r² + s²`. -/
def gaussNorm {n : ℕ} (p : ZMod n × ZMod n) : ZMod n := p.1 ^ 2 + p.2 ^ 2

/-- The norm is multiplicative for the Gaussian product (`|zw|² = |z|²|w|²`). -/
lemma gaussNorm_gaussMul {n : ℕ} (p q : ZMod n × ZMod n) :
    gaussNorm (gaussMul p q) = gaussNorm p * gaussNorm q := by
  simp only [gaussNorm, gaussMul]
  ring

/-- The Gaussian product is commutative. -/
lemma gaussMul_comm {n : ℕ} (p q : ZMod n × ZMod n) : gaussMul p q = gaussMul q p := by
  simp only [gaussMul]
  ext <;> ring

/-- The Gaussian product is associative. -/
lemma gaussMul_assoc {n : ℕ} (p q r : ZMod n × ZMod n) :
    gaussMul (gaussMul p q) r = gaussMul p (gaussMul q r) := by
  simp only [gaussMul]
  ext <;> ring

/-- `(1,0)` is the identity for the Gaussian product. -/
lemma gaussMul_one {n : ℕ} (p : ZMod n × ZMod n) : gaussMul p (1, 0) = p := by
  simp only [gaussMul]
  ext <;> ring

/-- The identity `(1,0)` is also a left identity. -/
lemma gaussMul_one_left {n : ℕ} (p : ZMod n × ZMod n) : gaussMul (1, 0) p = p := by
  rw [gaussMul_comm]
  exact gaussMul_one p

/-- **The inverse in coordinates**: `(r,s)⁻¹ = (r t, −s t)` with `t = (r²+s²)⁻¹` is a right
inverse of `(r,s)` whenever the norm is a unit (`gaussMod_exists_inv_iff`). -/
lemma gaussMul_inv_cancel {n : ℕ} (p : ZMod n × ZMod n) (h : IsUnit (gaussNorm p)) :
    gaussMul p (p.1 * (gaussNorm p)⁻¹, -(p.2 * (gaussNorm p)⁻¹)) = (1, 0) := by
  have h1 : gaussNorm p * (gaussNorm p)⁻¹ = 1 := ZMod.mul_inv_of_unit _ h
  have h2 : p.1 ^ 2 + p.2 ^ 2 = gaussNorm p := rfl
  ext
  · simp only [gaussMul]
    rw [← h1, ← h2]
    ring
  · simp only [gaussMul]
    ring

/-! ## The group structure on the Gaussian units -/

/-- **The Gaussian unit group of `ℤ[i]/n`, in coordinates**: `(r,s)` with `r² + s²` a unit of
`ZMod n`, with product `gaussMul`, identity `(1,0)` and inverse `(r,s)⁻¹ = (r t, −s t)`,
`t = (r²+s²)⁻¹` (`gaussMul_inv_cancel`).  Closure of `IsUnit` under the product is
`gaussNorm_gaussMul`; the laws are the four lemmas above; `div`/`zpow` are the `DivInvMonoid`
defaults. -/
instance gaussUnitsCommGroup (n : ℕ) :
    CommGroup {p : ZMod n × ZMod n // IsUnit (gaussNorm p)} where
  mul x y := ⟨gaussMul x.1 y.1, by rw [gaussNorm_gaussMul]; exact x.2.mul y.2⟩
  one := ⟨(1, 0), by simp [gaussNorm]⟩
  inv x := ⟨(x.1.1 * (gaussNorm x.1)⁻¹, -(x.1.2 * (gaussNorm x.1)⁻¹)), by
    have hN : x.1.1 ^ 2 + x.1.2 ^ 2 = gaussNorm x.1 := rfl
    have h : (x.1.1 ^ 2 + x.1.2 ^ 2) * (x.1.1 ^ 2 + x.1.2 ^ 2)⁻¹ = 1 := by
      rw [hN]
      exact ZMod.mul_inv_of_unit (gaussNorm x.1) x.2
    have hnorm : gaussNorm (x.1.1 * (gaussNorm x.1)⁻¹, -(x.1.2 * (gaussNorm x.1)⁻¹))
        = (x.1.1 ^ 2 + x.1.2 ^ 2)⁻¹ := by
      simp only [gaussNorm]
      calc (x.1.1 * (x.1.1 ^ 2 + x.1.2 ^ 2)⁻¹) ^ 2
              + (-(x.1.2 * (x.1.1 ^ 2 + x.1.2 ^ 2)⁻¹)) ^ 2
          = (x.1.1 ^ 2 + x.1.2 ^ 2) * (x.1.1 ^ 2 + x.1.2 ^ 2)⁻¹
              * (x.1.1 ^ 2 + x.1.2 ^ 2)⁻¹ := by ring
        _ = 1 * (x.1.1 ^ 2 + x.1.2 ^ 2)⁻¹ := by rw [h]
        _ = (x.1.1 ^ 2 + x.1.2 ^ 2)⁻¹ := one_mul _
    rw [hnorm]
    have h' : ((x.1.1 ^ 2 + x.1.2 ^ 2)⁻¹) * (x.1.1 ^ 2 + x.1.2 ^ 2) = 1 := by
      rw [mul_comm]; exact h
    exact isUnit_iff_exists_inv.mpr ⟨x.1.1 ^ 2 + x.1.2 ^ 2, h'⟩⟩
  mul_assoc x y z := Subtype.ext (gaussMul_assoc x.1 y.1 z.1)
  one_mul x := Subtype.ext (gaussMul_one_left x.1)
  mul_one x := Subtype.ext (gaussMul_one x.1)
  inv_mul_cancel x := Subtype.ext (by
    show gaussMul (x.1.1 * (gaussNorm x.1)⁻¹, -(x.1.2 * (gaussNorm x.1)⁻¹)) x.1 = (1, 0)
    rw [gaussMul_comm]
    exact gaussMul_inv_cancel x.1 x.2)
  mul_comm x y := Subtype.ext (gaussMul_comm x.1 y.1)

end Work.FIArea7
