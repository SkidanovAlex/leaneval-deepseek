import Mathlib
import Submission.Work.KT.Defs
import Submission.Work.KT.PsiC.BFrame

/-!
# `Work.PsiC.DepsDefs` — the generic `ε`-projector of an element of a `ℂ`-algebra

For an element `x` of a `ℂ`-algebra `R` we write

`hps ε x = (1/2) • (1 + ε • x)`,

the `ε`-eigenprojector of an involution `x`.  For a permutation `σ` the matrix
`hps ε (σ.permMatrix A)` is exactly `halfProj ε σ` (`Work.KT.PsiC.halfProj`), so all the
identities about the joint projector `Eeps ε n = Π_j halfProj ε (sg_j)` and about
`Deps ε n = halfProj ε (sB n) - Eeps ε n` can be proved once, abstractly, in an arbitrary ring,
and then instantiated.

Main results of this file (all in an arbitrary ring `R` with `[Algebra ℂ R]`):

* `hps_idem`, `comm_hps`, `hps_comm`, `x_mul_hps`, `hps_mul_x` — the pointwise projector
  identities: `hps ε x` is idempotent, commutes with everything commuting with `x`, and is an
  `ε`-eigenvector for `x` on both sides;
* `idem_mul_of_comm` — a product of two commuting idempotents is idempotent;
* `rearrange3` — a rearrangement of two length-three products with matching commutations;
* `hps_package` — for three involutions `x,y,z` that commute pairwise, the joint projector
  `E = hps ε x * hps ε y * hps ε z` and the "product" projector `H = hps ε (x*y*z)` satisfy
  `E * E = E`, `H * H = H`, `H * E = E` and `E * H = E`.
* `sub_facts` — for idempotents `H`, `E` with `H * E = E * H`-free hypotheses
  (`H*H = H`, `E*E = E`, `H*E = E`, `E*H = E`), the difference `H - E` is idempotent and
  orthogonal to `E`, and `E + (H - E) = H`.
-/

namespace Work.PsiC

namespace DepsAux

noncomputable section

variable {R : Type} [Ring R] [Algebra ℂ R]

/-- The `ε`-projector `(1/2)(1 + εx)` of an element `x`. -/
def hps (ε : ℂ) (x : R) : R := ((1:ℂ)/2) • (1 + ε • x)

/-- Scalar bookkeeping: `(a • X) * (b • Y) = (a b) • (X Y)`. -/
theorem smul_mul_smulC (a b : ℂ) (X Y : R) : (a • X) * (b • Y) = (a*b) • (X*Y) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul]

/-- `Y + Y = 2 • Y` with the scalar `2` read in `ℂ`. -/
theorem two_smulC (Y : R) : Y + Y = (2:ℂ) • Y := by
  rw [Algebra.smul_def, map_ofNat, two_mul]

/-- `a * (b * X) = b * (a * X)` when `a` and `b` commute. -/
theorem swap_mul {a b : R} (h : a * b = b * a) (X : R) : a * (b * X) = b * (a * X) := by
  rw [← mul_assoc, h, mul_assoc]

/-! ## Pointwise identities for `hps` -/

/-- `hps ε x` is idempotent for an involution `x` and `ε² = 1`. -/
theorem hps_idem (ε : ℂ) (heps : ε ^ 2 = 1) (x : R) (hx : x * x = 1) :
    hps ε x * hps ε x = hps ε x := by
  have he : ε * ε = 1 := by rw [← pow_two]; exact heps
  have huu : (ε • x) * (ε • x) = 1 := by rw [smul_mul_smulC, he, one_smul, hx]
  have h1 : (1 + ε • x) * (1 + ε • x) = (1 + ε • x) + (1 + ε • x) := by
    rw [add_mul, one_mul, mul_add, mul_one, huu, add_comm (ε • x) 1, ← add_assoc]
  rw [hps]
  calc ((1:ℂ)/2) • (1 + ε • x) * (((1:ℂ)/2) • (1 + ε • x))
      = (((1:ℂ)/2) * ((1:ℂ)/2)) • ((1 + ε • x) * (1 + ε • x)) := by rw [smul_mul_smulC]
    _ = (((1:ℂ)/2) * ((1:ℂ)/2)) • ((1 + ε • x) + (1 + ε • x)) := by rw [h1]
    _ = (((1:ℂ)/2) * ((1:ℂ)/2)) • ((2:ℂ) • (1 + ε • x)) := by rw [two_smulC]
    _ = ((((1:ℂ)/2) * ((1:ℂ)/2)) * 2) • (1 + ε • x) := by rw [smul_smul]
    _ = ((1:ℂ)/2) • (1 + ε • x) := by
        rw [show (((1:ℂ)/2) * ((1:ℂ)/2)) * 2 = (1:ℂ)/2 by norm_num]

/-- `hps ε x` commutes with everything commuting with `x`. -/
theorem comm_hps (ε : ℂ) {x y : R} (hyx : y * x = x * y) : y * hps ε x = hps ε x * y := by
  have h1 : y * hps ε x = ((1:ℂ)/2) • (y + ε • (y * x)) := by
    rw [hps, mul_smul_comm, mul_add, mul_one, mul_smul_comm]
  have h2 : hps ε x * y = ((1:ℂ)/2) • (y + ε • (x * y)) := by
    rw [hps, smul_mul_assoc, add_mul, one_mul, smul_mul_assoc]
  rw [h1, h2, hyx]

/-- `hps ε x` and `hps ε y` commute when `x` and `y` do. -/
theorem hps_comm (ε : ℂ) {x y : R} (hxy : x * y = y * x) :
    hps ε x * hps ε y = hps ε y * hps ε x :=
  comm_hps ε (x := y) (y := hps ε x) (comm_hps ε (x := x) (y := y) hxy.symm).symm

/-- `x` acts on `hps ε x` by the scalar `ε` (on the left). -/
theorem x_mul_hps (ε : ℂ) (heps : ε ^ 2 = 1) (x : R) (hx : x * x = 1) :
    x * hps ε x = ε • hps ε x := by
  have he : ε * ε = 1 := by rw [← pow_two]; exact heps
  have haux : ε • (((1:ℂ)/2) • (1 + ε•x)) = ((1:ℂ)/2) • (x + ε • 1) := by
    rw [smul_smul, mul_comm ε ((1:ℂ)/2), ← smul_smul, smul_add]
    rw [smul_smul, he, one_smul, add_comm]
  have hL : x * hps ε x = ((1:ℂ)/2) • (x + ε • 1) := by
    rw [hps, mul_smul_comm, mul_add, mul_one, mul_smul_comm, hx]
  rw [hL, hps, haux]

/-- `x` acts on `hps ε x` by the scalar `ε` (on the right). -/
theorem hps_mul_x (ε : ℂ) (heps : ε ^ 2 = 1) (x : R) (hx : x * x = 1) :
    hps ε x * x = ε • hps ε x := by
  have he : ε * ε = 1 := by rw [← pow_two]; exact heps
  have haux : ε • (((1:ℂ)/2) • (1 + ε•x)) = ((1:ℂ)/2) • (x + ε • 1) := by
    rw [smul_smul, mul_comm ε ((1:ℂ)/2), ← smul_smul, smul_add]
    rw [smul_smul, he, one_smul, add_comm]
  have hL : hps ε x * x = ((1:ℂ)/2) • (x + ε • 1) := by
    rw [hps, smul_mul_assoc, add_mul, one_mul, smul_mul_assoc, hx]
  rw [hL, hps, haux]

/-! ## Two- and three-factor products -/

/-- A product of two commuting idempotents is idempotent. -/
theorem idem_mul_of_comm {a b : R} (ha : a * a = a) (hb : b * b = b) (hab : a * b = b * a) :
    (a * b) * (a * b) = a * b := by
  calc (a * b) * (a * b) = a * (b * a) * b := by noncomm_ring
    _ = a * (a * b) * b := by rw [← hab]
    _ = (a * a) * (b * b) := by noncomm_ring
    _ = a * b := by rw [ha, hb]

/-- Rearrangement of two length-three products with matching commutations:
`(a b c)(p q r) = (a p)(b q)(c r)`. -/
theorem rearrange3 (a b c p q r : R) (hbp : b * p = p * b) (hcp : c * p = p * c)
    (hcq : c * q = q * c) :
    (a * b * c) * (p * q * r) = (a * p) * (b * q) * (c * r) := by
  have e1 : c * (p * (q * r)) = p * (q * (c * r)) := by
    calc c * (p * (q * r)) = (c * p) * (q * r) := by rw [mul_assoc]
      _ = (p * c) * (q * r) := by rw [hcp]
      _ = p * (c * (q * r)) := by rw [mul_assoc]
      _ = p * ((c * q) * r) := by rw [mul_assoc]
      _ = p * ((q * c) * r) := by rw [hcq]
      _ = p * (q * (c * r)) := by rw [mul_assoc]
  calc (a * b * c) * (p * q * r) = a * (b * (c * (p * (q * r)))) := by noncomm_ring
    _ = a * (b * (p * (q * (c * r)))) := by rw [e1]
    _ = a * (p * (b * (q * (c * r)))) := by rw [swap_mul hbp]
    _ = (a * p) * (b * q) * (c * r) := by noncomm_ring

/-- **The joint-projector package.**  For pairwise commuting involutions `x, y, z` and `ε² = 1`,
the joint projector `E = hps ε x * hps ε y * hps ε z` and the projector `H = hps ε (x*y*z)` of the
product are idempotent, and `H * E = E`, `E * H = E`. -/
theorem hps_package (ε : ℂ) (heps : ε ^ 2 = 1) (x y z : R)
    (hx : x * x = 1) (hy : y * y = 1) (hz : z * z = 1)
    (hxy : x * y = y * x) (hxz : x * z = z * x) (hyz : y * z = z * y) :
    (hps ε x * hps ε y * hps ε z) * (hps ε x * hps ε y * hps ε z) =
        hps ε x * hps ε y * hps ε z ∧
    hps ε (x * y * z) * hps ε (x * y * z) = hps ε (x * y * z) ∧
    hps ε (x * y * z) * (hps ε x * hps ε y * hps ε z) = hps ε x * hps ε y * hps ε z ∧
    (hps ε x * hps ε y * hps ε z) * hps ε (x * y * z) = hps ε x * hps ε y * hps ε z := by
  have he : ε * ε = 1 := by rw [← pow_two]; exact heps
  have i0 : hps ε x * hps ε x = hps ε x := hps_idem ε heps x hx
  have i1 : hps ε y * hps ε y = hps ε y := hps_idem ε heps y hy
  have i2 : hps ε z * hps ε z = hps ε z := hps_idem ε heps z hz
  have c01 : hps ε x * hps ε y = hps ε y * hps ε x := hps_comm ε hxy
  have c02 : hps ε x * hps ε z = hps ε z * hps ε x := hps_comm ε hxz
  have c12 : hps ε y * hps ε z = hps ε z * hps ε y := hps_comm ε hyz
  have a0L : x * hps ε x = ε • hps ε x := x_mul_hps ε heps x hx
  have a1L : y * hps ε y = ε • hps ε y := x_mul_hps ε heps y hy
  have a2L : z * hps ε z = ε • hps ε z := x_mul_hps ε heps z hz
  have a0R : hps ε x * x = ε • hps ε x := hps_mul_x ε heps x hx
  have a1R : hps ε y * y = ε • hps ε y := hps_mul_x ε heps y hy
  have a2R : hps ε z * z = ε • hps ε z := hps_mul_x ε heps z hz
  have hEE : (hps ε x * hps ε y * hps ε z) * (hps ε x * hps ε y * hps ε z) =
      hps ε x * hps ε y * hps ε z := by
    have h01 : (hps ε x * hps ε y) * (hps ε x * hps ε y) = hps ε x * hps ε y :=
      idem_mul_of_comm i0 i1 c01
    have hc : (hps ε x * hps ε y) * hps ε z = hps ε z * (hps ε x * hps ε y) := by
      calc (hps ε x * hps ε y) * hps ε z = hps ε x * (hps ε y * hps ε z) := by
            noncomm_ring
        _ = hps ε x * (hps ε z * hps ε y) := by rw [c12]
        _ = (hps ε x * hps ε z) * hps ε y := by noncomm_ring
        _ = (hps ε z * hps ε x) * hps ε y := by rw [c02]
        _ = hps ε z * (hps ε x * hps ε y) := by noncomm_ring
    exact idem_mul_of_comm h01 i2 hc
  have hs : (x * y * z) * (x * y * z) = 1 := by
    have s_yx : ∀ t : R, y * (x * t) = x * (y * t) := fun t => swap_mul hxy.symm t
    have s_zx : ∀ t : R, z * (x * t) = x * (z * t) := fun t => swap_mul hxz.symm t
    have s_zy : ∀ t : R, z * (y * t) = y * (z * t) := fun t => swap_mul hyz.symm t
    simp only [mul_assoc, s_yx, s_zx, s_zy, hx, hy, hz, mul_one]
  have hHH : hps ε (x * y * z) * hps ε (x * y * z) = hps ε (x * y * z) :=
    hps_idem ε heps (x * y * z) hs
  have hsE : (x * y * z) * (hps ε x * hps ε y * hps ε z) =
      ε • (hps ε x * hps ε y * hps ε z) := by
    rw [rearrange3 (a := x) (b := y) (c := z) (p := hps ε x) (q := hps ε y) (r := hps ε z)
      (comm_hps ε (x := x) (y := y) hxy.symm)
      (comm_hps ε (x := x) (y := z) hxz.symm)
      (comm_hps ε (x := y) (y := z) hyz.symm)]
    rw [a0L, a1L, a2L, smul_mul_smulC, smul_mul_smulC,
      show (ε*ε)*ε = ε by rw [he, one_mul]]
  have hEs : (hps ε x * hps ε y * hps ε z) * (x * y * z) =
      ε • (hps ε x * hps ε y * hps ε z) := by
    rw [rearrange3 (a := hps ε x) (b := hps ε y) (c := hps ε z) (p := x) (q := y) (r := z)
      (comm_hps ε (x := y) (y := x) hxy).symm
      (comm_hps ε (x := z) (y := x) hxz).symm
      (comm_hps ε (x := z) (y := y) hyz).symm]
    rw [a0R, a1R, a2R, smul_mul_smulC, smul_mul_smulC,
      show (ε*ε)*ε = ε by rw [he, one_mul]]
  have hHE : hps ε (x * y * z) * (hps ε x * hps ε y * hps ε z) =
      hps ε x * hps ε y * hps ε z := by
    calc hps ε (x * y * z) * (hps ε x * hps ε y * hps ε z)
        = (((1:ℂ)/2) • (1 + ε • (x*y*z))) * (hps ε x * hps ε y * hps ε z) := rfl
      _ = ((1:ℂ)/2) • ((1 + ε • (x*y*z)) * (hps ε x * hps ε y * hps ε z)) := by
            rw [smul_mul_assoc]
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) +
            (ε • (x*y*z)) * (hps ε x * hps ε y * hps ε z)) := by rw [add_mul, one_mul]
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) +
            ε • ((x*y*z) * (hps ε x * hps ε y * hps ε z))) := by rw [smul_mul_assoc]
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) +
            ε • (ε • (hps ε x * hps ε y * hps ε z))) := by rw [hsE]
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) +
            (ε*ε) • (hps ε x * hps ε y * hps ε z)) := by rw [smul_smul]
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) +
            (1:ℂ) • (hps ε x * hps ε y * hps ε z)) := by rw [he]
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) +
            (hps ε x * hps ε y * hps ε z)) := by rw [one_smul]
      _ = ((1:ℂ)/2) • ((2:ℂ) • (hps ε x * hps ε y * hps ε z)) := by rw [two_smulC]
      _ = (((1:ℂ)/2) * 2) • (hps ε x * hps ε y * hps ε z) := by rw [smul_smul]
      _ = hps ε x * hps ε y * hps ε z := by
            rw [show ((1:ℂ)/2) * 2 = 1 by norm_num, one_smul]
  have hEH : (hps ε x * hps ε y * hps ε z) * hps ε (x * y * z) =
      hps ε x * hps ε y * hps ε z := by
    calc (hps ε x * hps ε y * hps ε z) * hps ε (x * y * z)
        = (hps ε x * hps ε y * hps ε z) * (((1:ℂ)/2) • (1 + ε • (x*y*z))) := rfl
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) * (1 + ε • (x*y*z))) := by
            rw [mul_smul_comm]
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) +
            (hps ε x * hps ε y * hps ε z) * (ε • (x*y*z))) := by rw [mul_add, mul_one]
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) +
            ε • ((hps ε x * hps ε y * hps ε z) * (x*y*z))) := by rw [mul_smul_comm]
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) +
            ε • (ε • (hps ε x * hps ε y * hps ε z))) := by rw [hEs]
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) +
            (ε*ε) • (hps ε x * hps ε y * hps ε z)) := by rw [smul_smul]
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) +
            (1:ℂ) • (hps ε x * hps ε y * hps ε z)) := by rw [he]
      _ = ((1:ℂ)/2) • ((hps ε x * hps ε y * hps ε z) +
            (hps ε x * hps ε y * hps ε z)) := by rw [one_smul]
      _ = ((1:ℂ)/2) • ((2:ℂ) • (hps ε x * hps ε y * hps ε z)) := by rw [two_smulC]
      _ = (((1:ℂ)/2) * 2) • (hps ε x * hps ε y * hps ε z) := by rw [smul_smul]
      _ = hps ε x * hps ε y * hps ε z := by
            rw [show ((1:ℂ)/2) * 2 = 1 by norm_num, one_smul]
  exact ⟨hEE, hHH, hHE, hEH⟩

/-- From `H * H = H`, `E * E = E`, `H * E = E` and `E * H = E` the difference `H - E` is
idempotent, orthogonal to `E` on both sides, and `E + (H - E) = H`. -/
theorem sub_facts {H E : R} (hH : H * H = H) (hE : E * E = E)
    (hHE : H * E = E) (hEH : E * H = E) :
    (H - E) * (H - E) = H - E ∧ (H - E) * E = 0 ∧ E * (H - E) = 0 ∧ E + (H - E) = H := by
  have h1 : (H - E) * (H - E) = H - E := by
    rw [sub_mul, mul_sub, mul_sub, hH, hHE, hEH, hE, sub_self, sub_zero]
  have h2 : (H - E) * E = 0 := by rw [sub_mul, hHE, hE, sub_self]
  have h3 : E * (H - E) = 0 := by rw [mul_sub, hEH, hE, sub_self]
  have h4 : E + (H - E) = H := add_sub_cancel E H
  exact ⟨h1, h2, h3, h4⟩

end

end DepsAux

end Work.PsiC
