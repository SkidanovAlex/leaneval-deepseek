import Mathlib
import Submission.Work.Pi6.MSS.e2Aux
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.PageData
import Submission.Work.Pi6.MSS.pdMulAssoc
import Submission.Work.Pi6.MSS.mssMulCompat
import Submission.Work.Pi6.MSS.mssMulAssoc
import Submission.Work.Pi6.Interfaces
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Koszul rule for the `E_2` product of the Serre spectral sequence

`Work.Pi6.MSS.mulKoszul`: if the bottom row `E_2^{s,0}` and the zeroth column `E_2^{0,q}` of the
Serre spectral sequence of a fibration carry multiplicative systems of classes
(`row`, `col`), which graded-commute with the sign `(-1)^{s q}` (`hcomm`), then the product of the
page satisfies the Koszul rule

`(row s b · col q f) · (row s' b' · col q' f') = (-1)^{q s'} · (row (s+s') (b ⌣ b') · col (q+q') (f ⌣ f'))`.

The proof is purely formal: associativity of the page product, together with the three given
relations, determines the reordering of the four factors.

## Cast infrastructure

The product `mssMul` on the bidegree-indexed pages of `AssembleCore.lean` is a transport of the
concrete product `pd_mul` along index identifications; the lemmas below (`mssCast_trans`,
`mssMul_cast`, `mssMul_cast_arg1`, `mssMul_cast_arg2`) move these transports through the product.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜}

/-- Transports of bidegree-indexed pages along equalities of bidegrees compose. -/
theorem mssCast_trans {r : ℕ} {x y z : ℤ × ℤ} (h1 : x = y) (h2 : y = z)
    (v : mssE 𝕜 W r x) :
    mssCast 𝕜 W r h2 (mssCast 𝕜 W r h1 v) = mssCast 𝕜 W r (h1.trans h2) v := by
  rw [mssCast_eq_pCast 𝕜 W r h1, mssCast_eq_pCast 𝕜 W r h2,
    mssCast_eq_pCast 𝕜 W r (h1.trans h2)]
  rw [pCast_comp_apply]

/-- The product on the pages only depends on the bidegree of its value through the obvious transport:
if `c = c'` then `mssCast` carries the product landing in `c` to the product landing in `c'`. -/
theorem mssMul_cast {r : ℕ} {a b c c' : ℤ × ℤ} (h1 : a + b = c) (h2 : a + b = c')
    (hc : c = c') (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) :
    mssCast 𝕜 W r hc (mssMul 𝕜 W r a b c h1 x y) = mssMul 𝕜 W r a b c' h2 x y := by
  simp only [mssMul, LinearMap.comp_apply, LinearMap.llcomp_apply]
  rw [mssCast_trans]

/-- Naturality of the page product in its first argument with respect to bidegree transports. -/
theorem mssMul_cast_arg1 {r : ℕ} {a a' b c : ℤ × ℤ}
    (ha : a = a') (h1 : a' + b = c) (hc : a + b = c)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) :
    mssMul 𝕜 W r a' b c h1 (mssCast 𝕜 W r ha x) y
      = mssCast 𝕜 W r hc (mssMul 𝕜 W r a b (a + b) (rfl : a + b = a + b) x y) := by
  rw [mssMul_self_apply]
  change mssCast 𝕜 W r h1 (mssMulRaw 𝕜 W r a' b (mssCast 𝕜 W r ha x) y)
    = mssCast 𝕜 W r hc (mssMulRaw 𝕜 W r a b x y)
  simp only [mssCast_apply]
  by_cases hbE : Enn b
  · by_cases haE : Enn a
    · have haE' : Enn a' := ha ▸ haE
      simp only [mssMulRaw_apply_enn haE' hbE, mssMulRaw_apply_enn haE hbE]
      conv_lhs => rw [pd_mul_pEcast_left]
      rw [pEcast_hom_apply_comp, pEcast_hom_apply_comp, pEcast_hom_apply_comp]
    · have haE' : ¬ Enn a' := fun h => haE (ha ▸ h)
      simp only [mssMulRaw_apply_neg haE', mssMulRaw_apply_neg haE, map_zero]
  · simp only [mssMulRaw_eq_zero_right hbE, LinearMap.zero_apply, map_zero]

/-- Naturality of the page product in its second argument with respect to bidegree transports. -/
theorem mssMul_cast_arg2 {r : ℕ} {a b b' c : ℤ × ℤ}
    (hb : b = b') (h1 : a + b' = c) (hc : a + b = c)
    (x : mssE 𝕜 W r a) (y : mssE 𝕜 W r b) :
    mssMul 𝕜 W r a b' c h1 x (mssCast 𝕜 W r hb y)
      = mssCast 𝕜 W r hc (mssMul 𝕜 W r a b (a + b) (rfl : a + b = a + b) x y) := by
  rw [mssMul_self_apply]
  change mssCast 𝕜 W r h1 (mssMulRaw 𝕜 W r a b' x (mssCast 𝕜 W r hb y))
    = mssCast 𝕜 W r hc (mssMulRaw 𝕜 W r a b x y)
  simp only [mssCast_apply]
  by_cases haE : Enn a
  · by_cases hbE : Enn b
    · have hbE' : Enn b' := hb ▸ hbE
      simp only [mssMulRaw_apply_enn haE hbE', mssMulRaw_apply_enn haE hbE]
      conv_lhs => rw [pd_mul_pEcast_right]
      rw [pEcast_hom_apply_comp, pEcast_hom_apply_comp, pEcast_hom_apply_comp]
    · have hbE' : ¬ Enn b' := fun h => hbE (hb ▸ h)
      simp only [mssMulRaw_eq_zero_right hbE', mssMulRaw_eq_zero_right hbE,
        LinearMap.zero_apply, map_zero]
  · simp only [mssMulRaw_apply_neg haE, map_zero]

section Notation

variable (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
local notation "M₂" => mssMul _ _ 2
local notation "CA" => mssCast _ _ 2

theorem mulKoszul (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E)
    (row : ∀ s : ℕ, Work.Pi6.Coh 𝕜 B s →ₗ[𝕜]
      Work.Pi6.MSS.mssE 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)))
    (col : ∀ q : ℕ, Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q →ₗ[𝕜]
      Work.Pi6.MSS.mssE 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)))
    (hrow : ∀ (s s' : ℕ) (b : Work.Pi6.Coh 𝕜 B s) (b' : Work.Pi6.Coh 𝕜 B s'),
      row (s + s') (Work.Pi6.cup 𝕜 B s s' b b') =
        Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) ((s' : ℤ), (0 : ℤ))
          (((s + s' : ℕ) : ℤ), (0 : ℤ)) (by ext <;> simp) (row s b) (row s' b'))
    (hcol : ∀ (q q' : ℕ) (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
      (f' : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q'),
      col (q + q') (Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) q q' f f') =
        Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) ((0 : ℤ), (q' : ℤ))
          ((0 : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp) (col q f) (col q' f'))
    (hcomm : ∀ (s q : ℕ) (b : Work.Pi6.Coh 𝕜 B s)
      (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q),
      Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((0 : ℤ), (q : ℤ)) ((s : ℤ), (0 : ℤ))
          ((s : ℤ), (q : ℤ)) (by ext <;> simp) (col q f) (row s b) =
        (-1 : 𝕜) ^ (s * q) •
          Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) ((0 : ℤ), (q : ℤ))
            ((s : ℤ), (q : ℤ)) (by ext <;> simp) (row s b) (col q f)) :
    ∀ (s q s' q' : ℕ) (b : Work.Pi6.Coh 𝕜 B s)
      (f : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
      (b' : Work.Pi6.Coh 𝕜 B s') (f' : Work.Pi6.Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q'),
      Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ))
          (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp)
          (Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((s : ℤ), (0 : ℤ)) ((0 : ℤ), (q : ℤ))
            ((s : ℤ), (q : ℤ)) (by ext <;> simp) (row s b) (col q f))
          (Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 ((s' : ℤ), (0 : ℤ)) ((0 : ℤ), (q' : ℤ))
            ((s' : ℤ), (q' : ℤ)) (by ext <;> simp) (row s' b') (col q' f'))
        = (-1 : 𝕜) ^ (q * s') •
          Work.Pi6.MSS.mssMul 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 (((s + s' : ℕ) : ℤ), (0 : ℤ))
            ((0 : ℤ), ((q + q' : ℕ) : ℤ))
            (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ)) (by ext <;> simp)
            (row (s + s') (Work.Pi6.cup 𝕜 B s s' b b'))
            (col (q + q') (Work.Pi6.cup 𝕜 (Work.StemsB.fibre p (p e₀)) q q' f f')) := by
  intro s q s' q' b f b' f'
  -- the bidegrees
  let A1 : ℤ × ℤ := ((s : ℤ), (0 : ℤ))
  let A2 : ℤ × ℤ := ((0 : ℤ), (q : ℤ))
  let A3 : ℤ × ℤ := ((s' : ℤ), (0 : ℤ))
  let A4 : ℤ × ℤ := ((0 : ℤ), (q' : ℤ))
  let B1 : ℤ × ℤ := ((s : ℤ), (q : ℤ))
  let B2 : ℤ × ℤ := ((s' : ℤ), (q' : ℤ))
  let B3 : ℤ × ℤ := (((s + s' : ℕ) : ℤ), (0 : ℤ))
  let B4 : ℤ × ℤ := ((0 : ℤ), ((q + q' : ℕ) : ℤ))
  let S2 : ℤ × ℤ := (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
  let c12 : ℤ × ℤ := A1 + A2
  let c34 : ℤ × ℤ := A3 + A4
  let c13 : ℤ × ℤ := A1 + A3
  let c24 : ℤ × ℤ := A2 + A4
  let c23 : ℤ × ℤ := A2 + A3
  let D2 : ℤ × ℤ := ((s' : ℤ), (q : ℤ))
  let bc : ℤ × ℤ := A3 + c24
  let CORE : ℤ × ℤ := c12 + c34
  -- elementary index identities
  have hA : A1 + A2 = B1 := by simp only [A1, A2, B1]; ext <;> simp
  have hB : A3 + A4 = B2 := by simp only [A3, A4, B2]; ext <;> simp
  have hR : A1 + A3 = B3 := by simp only [A1, A3, B3]; ext <;> simp
  have hCc : A2 + A4 = B4 := by simp only [A2, A4, B4]; ext <;> simp
  have hAB : B1 + B2 = S2 := by simp only [B1, B2, S2]; ext <;> simp
  have hDD : B3 + B4 = S2 := by simp only [B3, B4, S2]; ext <;> simp
  have hCORE : CORE = S2 := by
    simp only [CORE, c12, c34, A1, A2, A3, A4, S2]; ext <;> simp
  have ha1 : A1 + bc = CORE := by
    simp only [bc, CORE, c24, c12, c34, A1, A2, A3, A4]; ext <;> simp
  have ha2 : A2 + c34 = bc := by
    simp only [bc, c24, c34, A2, A3, A4]; ext <;> simp
  have hb1 : c23 + A4 = bc := by
    simp only [bc, c23, c24, A2, A3, A4]; ext <;> simp
  have hc1 : A3 + c24 = bc := by simp only [bc]
  have hcore : c13 + c24 = CORE := by
    simp only [CORE, c12, c34, c13, c24, A1, A2, A3, A4]; ext <;> simp
  have h12B2 : c12 + B2 = S2 := by
    simp only [c12, A1, A2, B2, S2]; ext <;> simp
  have hc1234 : c12 + c34 = c12 + B2 := by
    simp only [c34, A3, A4, B2]; ext <;> simp
  have hS2' : c13 + c24 = S2 := by
    simp only [c13, c24, A1, A2, A3, A4, S2]; ext <;> simp
  have hCc2 : c13 + B4 = S2 := by
    simp only [c13, A1, A3, B4, S2]; ext <;> simp
  have hc1324 : c13 + c24 = c13 + B4 := by
    simp only [c24, A2, A4, B4]; ext <;> simp
  -- the four raw elements
  have hEnn1 : Enn A1 := Enn_pair s 0
  have hEnn2 : Enn A2 := Enn_pair 0 q
  have hEnn3 : Enn A3 := Enn_pair s' 0
  have hEnn4 : Enn A4 := Enn_pair 0 q'
  have hEnn34 : Enn c34 := Enn_add hEnn3 hEnn4
  have hEnn24 : Enn c24 := Enn_add hEnn2 hEnn4
  have hc23 : A2 + A3 = c23 := by simp only [c23]
  have hc32 : A3 + A2 = c23 := by simp only [c23, A2, A3]; ext <;> simp
  have hD2c23 : D2 = c23 := by simp only [D2, c23, A2, A3]; ext <;> simp
  have hA2A3D2 : A2 + A3 = D2 := by simp only [D2, A2, A3]; ext <;> simp
  have hA3A2D2 : A3 + A2 = D2 := by simp only [D2, A3, A2]; ext <;> simp
  -- the canonical pairwise products
  let XYc : mssE 𝕜 (serreCF 𝕜 E B p) 2 c12 := M₂ A1 A2 c12 (rfl : A1 + A2 = c12) (row s b) (col q f)
  let UVc : mssE 𝕜 (serreCF 𝕜 E B p) 2 c34 := M₂ A3 A4 c34 (rfl : A3 + A4 = c34) (row s' b') (col q' f')
  let XUc : mssE 𝕜 (serreCF 𝕜 E B p) 2 c13 := M₂ A1 A3 c13 (rfl : A1 + A3 = c13) (row s b) (row s' b')
  let YVc : mssE 𝕜 (serreCF 𝕜 E B p) 2 c24 := M₂ A2 A4 c24 (rfl : A2 + A4 = c24) (col q f) (col q' f')
  -- transports between the goal's bidegrees and the canonical ones
  have hiso12 : CA hA XYc = M₂ A1 A2 B1 hA (row s b) (col q f) :=
    mssMul_cast (rfl : A1 + A2 = c12) hA hA (row s b) (col q f)
  have hiso34 : CA hB UVc = M₂ A3 A4 B2 hB (row s' b') (col q' f') :=
    mssMul_cast (rfl : A3 + A4 = c34) hB hB (row s' b') (col q' f')
  have hiso13 : CA hR XUc = M₂ A1 A3 B3 hR (row s b) (row s' b') :=
    mssMul_cast (rfl : A1 + A3 = c13) hR hR (row s b) (row s' b')
  have hiso24 : CA hCc YVc = M₂ A2 A4 B4 hCc (col q f) (col q' f') :=
    mssMul_cast (rfl : A2 + A4 = c24) hCc hCc (col q f) (col q' f')
  -- (1) pull the transports out of the goal's left-hand side
  have e1 : M₂ B1 B2 S2 hAB (M₂ A1 A2 B1 hA (row s b) (col q f))
        (M₂ A3 A4 B2 hB (row s' b') (col q' f'))
      = CA (hc1234.trans h12B2) (M₂ c12 c34 CORE (rfl : c12 + c34 = CORE) XYc UVc) := by
    rw [← hiso12, ← hiso34]
    rw [mssMul_cast_arg1 hA hAB h12B2]
    rw [mssMul_cast_arg2 hB (rfl : c12 + B2 = c12 + B2) hc1234]
    rw [mssCast_trans]
  -- (iii) the same for the goal's right-hand side, in reverse
  have e3 : M₂ B3 B4 S2 hDD (M₂ A1 A3 B3 hR (row s b) (row s' b'))
        (M₂ A2 A4 B4 hCc (col q f) (col q' f'))
      = M₂ c13 c24 S2 hS2' XUc YVc := by
    rw [← hiso13, ← hiso24]
    rw [mssMul_cast_arg1 hR hDD hCc2]
    rw [mssMul_cast_arg2 hCc (rfl : c13 + B4 = c13 + B4) hc1324]
    rw [mssCast_trans]
    rw [mssMul_cast (rfl : c13 + c24 = c13 + c24) hS2' (hc1324.trans hCc2)]
  -- the canonical mixed commutation relation, in the bidegree `c23`
  have hcommC : M₂ A2 A3 c23 hc23 (col q f) (row s' b')
      = (-1 : 𝕜) ^ (q * s') • M₂ A3 A2 c23 hc32 (row s' b') (col q f) := by
    have h1 := congrArg (fun w => CA hD2c23 w) (hcomm s' q b' f)
    simp only [map_smul] at h1
    rw [mssMul_cast (h1 := hA2A3D2) (h2 := hc23) (hc := hD2c23)] at h1
    rw [mssMul_cast (h1 := hA3A2D2) (h2 := hc32) (hc := hD2c23)] at h1
    rw [show s' * q = q * s' from Nat.mul_comm s' q] at h1
    exact h1
  -- the core reordering
  have e2 : M₂ c12 c34 CORE (rfl : c12 + c34 = CORE) XYc UVc
      = (-1 : 𝕜) ^ (q * s') • M₂ c13 c24 CORE hcore XUc YVc := by
    have ha := mssMulAssoc 𝕜 E B p 2 A1 A2 c34 c12 bc CORE hEnn1 hEnn2 hEnn34
      (rfl : A1 + A2 = c12) ha2 (rfl : c12 + c34 = CORE) ha1 (row s b) (col q f) UVc
    have hb := (mssMulAssoc 𝕜 E B p 2 A2 A3 A4 c23 c34 bc hEnn2 hEnn3 hEnn4
      (rfl : A2 + A3 = c23) (rfl : A3 + A4 = c34) hb1 ha2 (col q f) (row s' b') (col q' f')).symm
    have he := mssMulAssoc 𝕜 E B p 2 A3 A2 A4 c23 c24 bc hEnn3 hEnn2 hEnn4 hc32
      (rfl : A2 + A4 = c24) hb1 (rfl : A3 + c24 = bc) (row s' b') (col q f) (col q' f')
    have hf := (mssMulAssoc 𝕜 E B p 2 A1 A3 c24 c13 bc CORE hEnn1 hEnn3 hEnn24
      (rfl : A1 + A3 = c13) (rfl : A3 + c24 = bc) hcore ha1 (row s b) (row s' b') YVc).symm
    calc M₂ c12 c34 CORE (rfl : c12 + c34 = CORE) XYc UVc
        = M₂ A1 bc CORE ha1 (row s b) (M₂ A2 c34 bc ha2 (col q f) UVc) := ha
      _ = M₂ A1 bc CORE ha1 (row s b)
            (M₂ c23 A4 bc hb1 (M₂ A2 A3 c23 (rfl : A2 + A3 = c23)
              (col q f) (row s' b')) (col q' f')) := by rw [hb]
      _ = M₂ A1 bc CORE ha1 (row s b)
            (M₂ c23 A4 bc hb1
              ((-1 : 𝕜) ^ (q * s') • M₂ A3 A2 c23 hc32 (row s' b') (col q f))
              (col q' f')) := by rw [hcommC]
      _ = (-1 : 𝕜) ^ (q * s') • M₂ A1 bc CORE ha1 (row s b)
            (M₂ c23 A4 bc hb1 (M₂ A3 A2 c23 hc32 (row s' b') (col q f))
              (col q' f')) := by rw [map_smul, LinearMap.smul_apply, map_smul]
      _ = (-1 : 𝕜) ^ (q * s') • M₂ A1 bc CORE ha1 (row s b)
            (M₂ A3 c24 bc (rfl : A3 + c24 = bc) (row s' b') YVc) := by rw [he]
      _ = (-1 : 𝕜) ^ (q * s') • M₂ c13 c24 CORE hcore XUc YVc := by rw [hf]
  -- assembly
  rw [hrow s s' b b', hcol q q' f f']
  rw [e1]
  rw [e2]
  rw [map_smul]
  rw [mssMul_cast hcore hS2' (hc1234.trans h12B2)]
  rw [← e3]

end Notation

end

end Work.Pi6.MSS
