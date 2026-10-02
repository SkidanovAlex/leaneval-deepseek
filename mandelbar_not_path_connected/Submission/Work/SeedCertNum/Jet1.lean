/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# First-order jets of the antiholomorphic iterate, over interval boxes (item A1)

This is the analytic core of item **A1** of the `SeedCertNum` contract
(`NOTES_LEAD_mandelbar_noncusp.md` §2.2): the *derivative data* of the iteration
`Z_n(u) = (T_{c(u)})^[n] (z(u))` needed to feed Krawczyk's criterion for the `ℝ³`-system

  `P₁ = Re (g z - z)`,  `P₂ = Im (g z - z)`,  `P₃ = ∏_{k<5} ‖T_c^k z‖² · 2^{10} - 1`,
  `c = x₀ + it`,  `g = (T_c)^[5]`  (`x₀` fixed),

at the tricorn `α`-root arc.

The domain is `E3 = ℝ × (ℝ × ℝ)` with coordinates `u = (Re z, Im z, Im c)` and the sup norm;
the *parameter* `x₀ = Re c` is kept fixed (a dyadic rational), so that the unknown is exactly
three-dimensional.

## Contents

* `E3`, `zOf`, `cOf`, `mkE`, and the identifications `zOf_mkE`, `cOf_mkE`;
* the iteration `Z x₀ n : E3 → ℂ` and its **Wirtinger pair** `p`, `q` together with the
  parameter derivative `s` (`pq`, `p`, `q`, `ss`);
* the real-linear maps `lin3`, `Lz`, `conjCLM`, `Lt` and the recursive derivative `LZ`, whose
  characterisation is `LZ_apply`:
  `LZ x₀ n u δ = p δz + q conj δz + s δt`,  `δz = δ.1 + i δ.2.1`, `δt = δ.2.2`;
* the box layer: `pbox`, `boxCI`, `boxV`, `boxPQ`, `boxS`, with their soundness `mem_boxV`,
  `mem_boxP`, `mem_boxQ`, `mem_boxS`.

The derivative pair obeys the recursion of `NOTES_LEAD` §2.2: with `w = T_c^n z`,
`p_{n+1} = 2 conj(w) conj(q_n)`, `q_{n+1} = 2 conj(w) conj(p_n)`, `s_{n+1} = i + 2 conj(w) conj(s_n)`
— note that for `T_c` itself `p = 0` and `q = 2 conj w`, which is why `p` starts at `1` (`Z_0 = z`)
and `p_1 = 0`.
-/
import Mathlib
import Submission.Work.SeedCertNum.TBox
import Submission.Work.SeedCertNum.NormSq

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

/-! ## The domain `ℝ³` and the two projections to `ℂ` -/

/-- `ℝ³ = ℝ × (ℝ × ℝ)` with coordinates `(Re z, Im z, Im c)`, carrying the sup norm. -/
abbrev E3 : Type := ℝ × ℝ × ℝ

/-- The complex point `z = u.1 + i·u.2.1`. -/
def zOf (u : E3) : ℂ := (u.1 : ℂ) + (u.2.1 : ℂ) * Complex.I

/-- The parameter `c = x₀ + i·u.2.2`. -/
def cOf (x₀ : ℝ) (u : E3) : ℂ := (x₀ : ℂ) + (u.2.2 : ℂ) * Complex.I

/-- `(z,t) ↦ (Re z, Im z, t)`. -/
def mkE (z : ℂ) (t : ℝ) : E3 := (z.re, z.im, t)

@[simp] theorem mkE_fst (z : ℂ) (t : ℝ) : (mkE z t).1 = z.re := rfl
@[simp] theorem mkE_snd_fst (z : ℂ) (t : ℝ) : (mkE z t).2.1 = z.im := rfl
@[simp] theorem mkE_snd_snd (z : ℂ) (t : ℝ) : (mkE z t).2.2 = t := rfl

@[simp] theorem zOf_mkE (z : ℂ) (t : ℝ) : zOf (mkE z t) = z := by
  simp only [zOf, mkE, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  exact Complex.re_add_im z

@[simp] theorem cOf_mkE (x₀ : ℝ) (z : ℂ) (t : ℝ) : cOf x₀ (mkE z t) = x₀ + t * Complex.I :=
  rfl

@[simp] theorem zOf_apply (u : E3) : zOf u = (u.1 : ℂ) + (u.2.1 : ℂ) * Complex.I := rfl

@[simp] theorem cOf_apply (x₀ : ℝ) (u : E3) : cOf x₀ u = (x₀ : ℂ) + (u.2.2 : ℂ) * Complex.I := rfl

/-- The conjugate of `zOf u`, written out. -/
def conjZ (u : E3) : ℂ := (u.1 : ℂ) - (u.2.1 : ℂ) * Complex.I

@[simp] theorem conjZ_eq (u : E3) : conjZ u = star (zOf u) := by
  simp only [zOf_apply]
  simp [conjZ, Complex.conj_ofReal, Complex.conj_I]
  ring

@[simp] theorem star_conjZ (u : E3) : star (conjZ u) = zOf u := by
  rw [conjZ_eq, star_star]

@[simp] theorem star_zOf (u : E3) : star (zOf u) = conjZ u := by
  rw [← conjZ_eq]

/-! ## The iteration and its jets -/

/-- `Z x₀ n u = (T_{c(u)})^[n] (z(u))`, the `n`-th iterate of the antiholomorphic quadratic. -/
def Z (x₀ : ℝ) : ℕ → E3 → ℂ
  | 0 => zOf
  | n + 1 => fun u => star (Z x₀ n u) ^ 2 + cOf x₀ u

@[simp] theorem Z_zero (x₀ : ℝ) : Z x₀ 0 = zOf := rfl

@[simp] theorem Z_succ (x₀ : ℝ) (n : ℕ) (u : E3) :
    Z x₀ (n + 1) u = star (Z x₀ n u) ^ 2 + cOf x₀ u := rfl

/-- The pair `(p,q)` of `Z_n`: `fderiv ℝ (Z_n) u δ = p δz + q conj δz + s δt` (see `LZ_apply`).
Recursion: `p_{n+1} = 2 conj(Z_n) conj(q_n)`, `q_{n+1} = 2 conj(Z_n) conj(p_n)`. -/
def pq (x₀ : ℝ) : ℕ → E3 → ℂ × ℂ
  | 0 => fun _ => (1, 0)
  | n + 1 => fun u =>
      let w := star (Z x₀ n u)
      let z := pq x₀ n u
      (2 * w * star z.2, 2 * w * star z.1)

/-- The parameter derivative of `Z_n`: `d/dt (T_{x₀+it})^[n] z = s`. -/
def ss (x₀ : ℝ) : ℕ → E3 → ℂ
  | 0 => fun _ => 0
  | n + 1 => fun u => Complex.I + 2 * star (Z x₀ n u) * star (ss x₀ n u)

/-- The first Wirtinger coefficient of `Z_n`. -/
def p (x₀ : ℝ) (n : ℕ) (u : E3) : ℂ := (pq x₀ n u).1

/-- The second Wirtinger coefficient of `Z_n`. -/
def q (x₀ : ℝ) (n : ℕ) (u : E3) : ℂ := (pq x₀ n u).2

@[simp] theorem p_zero (x₀ : ℝ) (u : E3) : p x₀ 0 u = 1 := rfl
@[simp] theorem q_zero (x₀ : ℝ) (u : E3) : q x₀ 0 u = 0 := rfl
@[simp] theorem ss_zero (x₀ : ℝ) (u : E3) : ss x₀ 0 u = 0 := rfl

theorem p_succ (x₀ : ℝ) (n : ℕ) (u : E3) :
    p x₀ (n + 1) u = 2 * star (Z x₀ n u) * star (q x₀ n u) := rfl

theorem q_succ (x₀ : ℝ) (n : ℕ) (u : E3) :
    q x₀ (n + 1) u = 2 * star (Z x₀ n u) * star (p x₀ n u) := rfl

theorem ss_succ (x₀ : ℝ) (n : ℕ) (u : E3) :
    ss x₀ (n + 1) u = Complex.I + 2 * star (Z x₀ n u) * star (ss x₀ n u) := rfl

/-! ## The real-linear maps

`lin3 a b c` is `δ ↦ a·δ.1 + b·δ.2.1 + c·δ.2.2`, a real-linear map `E3 → ℂ`.  It is built with
`LinearMap.toContinuousLinearMap` so that `lin3 a b c δ` *reduces* to the explicit expression,
which keeps the certificate arithmetic cheap. -/

/-- The real-linear map `δ ↦ a·δ.1 + b·δ.2.1 + c·δ.2.2`, `E3 → ℂ`. -/
def lin3 (a b c : ℂ) : E3 →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun δ => a * (δ.1 : ℂ) + (δ.2.1 : ℂ) * b + (δ.2.2 : ℂ) * c
      map_add' := by
        intro x y
        simp only [Prod.fst_add, Prod.snd_add]
        push_cast
        ring
      map_smul' := by
        intro r x
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Complex.real_smul]
        push_cast
        simp only [id_eq]
        ring }

@[simp] theorem lin3_apply (a b c : ℂ) (δ : E3) :
    lin3 a b c δ = a * (δ.1 : ℂ) + (δ.2.1 : ℂ) * b + (δ.2.2 : ℂ) * c := rfl

/-- The real-linear map `δ ↦ δz = δ.1 + i·δ.2.1`. -/
def Lz : E3 →L[ℝ] ℂ := lin3 1 Complex.I 0

/-- The real-linear map `δ ↦ i·δ.2.2` (the derivative of `c ↦ c` in the `t`-direction). -/
def Lt : E3 →L[ℝ] ℂ := lin3 0 0 Complex.I

/-- Complex conjugation as a real-linear map. -/
def conjCLM : ℂ →L[ℝ] ℂ := (starL' ℝ : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap

@[simp] theorem conjCLM_apply (z : ℂ) : conjCLM z = star z := rfl

@[simp] theorem Lz_apply (δ : E3) : Lz δ = (δ.1 : ℂ) + (δ.2.1 : ℂ) * Complex.I := by
  simp [Lz, lin3_apply]

@[simp] theorem Lt_apply (δ : E3) : Lt δ = (δ.2.2 : ℂ) * Complex.I := by
  simp [Lt, lin3_apply]

/-- The unit vectors of `E3`, i.e. the three coordinate directions `∂/∂x`, `∂/∂y`, `∂/∂t`. -/
def eX : E3 := (1, 0, 0)

/-- The `y`-direction. -/
def eY : E3 := (0, 1, 0)

/-- The `t`-direction. -/
def eT : E3 := (0, 0, 1)

@[simp] theorem eX_fst : eX.1 = 1 := rfl
@[simp] theorem eX_snd_fst : eX.2.1 = 0 := rfl
@[simp] theorem eX_snd_snd : eX.2.2 = 0 := rfl
@[simp] theorem eY_fst : eY.1 = 0 := rfl
@[simp] theorem eY_snd_fst : eY.2.1 = 1 := rfl
@[simp] theorem eY_snd_snd : eY.2.2 = 0 := rfl
@[simp] theorem eT_fst : eT.1 = 0 := rfl
@[simp] theorem eT_snd_fst : eT.2.1 = 0 := rfl
@[simp] theorem eT_snd_snd : eT.2.2 = 1 := rfl

/-- The (Fréchet) derivative of `Z_n` at `u`, in the (p,q,s)-form
`δ ↦ p·δz + q·conj(δz) + s·δt` with `δz = δ.1 + i δ.2.1`.  Written as a `lin3` so that
`LZ_apply` is definitional. -/
def LZ (x₀ : ℝ) (n : ℕ) (u : E3) : E3 →L[ℝ] ℂ :=
  lin3 (p x₀ n u + q x₀ n u) (Complex.I * (p x₀ n u - q x₀ n u)) (ss x₀ n u)

theorem LZ_apply (x₀ : ℝ) (n : ℕ) (u δ : E3) :
    LZ x₀ n u δ = p x₀ n u * zOf δ + q x₀ n u * conjZ δ + ss x₀ n u * (δ.2.2 : ℂ) := by
  simp only [LZ, lin3_apply, zOf_apply, conjZ]
  ring

@[simp] theorem LZ_zero (x₀ : ℝ) (u : E3) : LZ x₀ 0 u = Lz := by
  apply ContinuousLinearMap.ext
  intro δ
  rw [LZ_apply, Lz_apply]
  simp only [p_zero, q_zero, ss_zero, zOf_apply, conjZ]
  ring

@[simp] theorem LZ_eX (x₀ : ℝ) (n : ℕ) (u : E3) : LZ x₀ n u eX = p x₀ n u + q x₀ n u := by
  simp only [LZ, lin3_apply]
  norm_num [eX]

@[simp] theorem LZ_eY (x₀ : ℝ) (n : ℕ) (u : E3) :
    LZ x₀ n u eY = Complex.I * (p x₀ n u - q x₀ n u) := by
  simp only [LZ, lin3_apply]
  norm_num [eY]

@[simp] theorem LZ_eT (x₀ : ℝ) (n : ℕ) (u : E3) : LZ x₀ n u eT = ss x₀ n u := by
  simp only [LZ, lin3_apply]
  norm_num [eT]

/-! ## The box layer

The boxes below are the mirror of the recursions of `p`, `q`, `s` at the level of interval
arithmetic: `boxV (n+1) = TBox Ctyp (boxV n)` (from `Submission/Work/SeedCertNum/TBox.lean`),
`boxPQ (n+1) = (2·conj(boxV n)) · conj(boxPQ n)` and
`boxS (n+1) = i + (2·conj(boxV n)) · conj(boxS n)`. -/

/-- The parameter box `{x₀ + i·t : t ∈ Xt}`. -/
def pbox (x₀ : Dya) (Xt : IV) : CBox := ⟨x₀, x₀, Xt.lo, Xt.hi⟩

/-- A box containing `i`. -/
def boxCI : CBox := ⟨Dya.zero, Dya.zero, Dya.one, Dya.one⟩

/-- The box enclosure of `Z_n` over `Xz × Xt`. -/
def boxV (Ctyp Xz : CBox) : ℕ → CBox
  | 0 => Xz
  | n + 1 => TBox Ctyp (boxV Ctyp Xz n)

/-- The box enclosure of the Wirtinger pair `(p,q)` of `Z_n` over `Xz × Xt`. -/
def boxPQ (Ctyp Xz : CBox) : ℕ → CBox × CBox
  | 0 => (⟨Dya.one, Dya.one, Dya.zero, Dya.zero⟩, ⟨Dya.zero, Dya.zero, Dya.zero, Dya.zero⟩)
  | n + 1 =>
      let w := ((boxV Ctyp Xz n).conj).mulScalar Dya.two
      let z := boxPQ Ctyp Xz n
      (w.mul z.2.conj, w.mul z.1.conj)

/-- The box enclosure of the parameter derivative `s` of `Z_n` over `Xz × Xt`. -/
def boxS (Ctyp Xz : CBox) : ℕ → CBox
  | 0 => ⟨Dya.zero, Dya.zero, Dya.zero, Dya.zero⟩
  | n + 1 =>
      boxCI.add ((((boxV Ctyp Xz n).conj).mulScalar Dya.two).mul (boxS Ctyp Xz n).conj)

/-! ### Soundness of the box layer -/

theorem mem_pbox {x₀ : Dya} {Xt : IV} {t : ℝ} (ht : t ∈ Xt.toSet) :
    ((x₀.toReal : ℝ) + t * Complex.I) ∈ (pbox x₀ Xt).toSet := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [pbox]
  · simp [pbox]
  · simpa [pbox] using ht.1
  · simpa [pbox] using ht.2

theorem mem_boxV (x₀ : Dya) (Xt : IV) (Xz : CBox) (n : ℕ) {z : ℂ} {t : ℝ}
    (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    Z x₀.toReal n (mkE z t) ∈ (boxV (pbox x₀ Xt) Xz n).toSet := by
  induction n with
  | zero => simpa [boxV] using hz
  | succ n ih =>
    have h := mem_TBox (Ctyp := pbox x₀ Xt) (B := boxV (pbox x₀ Xt) Xz n)
      (c := cOf x₀.toReal (mkE z t)) (z := Z x₀.toReal n (mkE z t))
      (by rw [cOf_mkE]; exact mem_pbox ht) ih
    simpa [boxV, Tantibar, Z_succ] using h

theorem mem_boxPQ (x₀ : Dya) (Xt : IV) (Xz : CBox) (n : ℕ) {z : ℂ} {t : ℝ}
    (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    p x₀.toReal n (mkE z t) ∈ (boxPQ (pbox x₀ Xt) Xz n).1.toSet ∧
      q x₀.toReal n (mkE z t) ∈ (boxPQ (pbox x₀ Xt) Xz n).2.toSet := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> simp [boxPQ, p, q, pq]
  | succ n ih =>
    have hV := mem_boxV x₀ Xt Xz n hz ht
    have h2 : (2 : ℂ) * star (Z x₀.toReal n (mkE z t)) ∈
        (((boxV (pbox x₀ Xt) Xz n).conj).mulScalar Dya.two).toSet := by
      have := CBox.mem_mulScalar (B := (boxV (pbox x₀ Xt) Xz n).conj)
        (CBox.mem_conj hV) (a := Dya.two)
      simpa [Dya.toReal_two] using this
    constructor
    · have h := Work.SeedCertNum.CBox_mem_mul h2 (CBox.mem_conj ih.2)
      simpa [boxPQ, p_succ] using h
    · have h := Work.SeedCertNum.CBox_mem_mul h2 (CBox.mem_conj ih.1)
      simpa [boxPQ, q_succ] using h

theorem mem_boxP (x₀ : Dya) (Xt : IV) (Xz : CBox) (n : ℕ) {z : ℂ} {t : ℝ}
    (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    p x₀.toReal n (mkE z t) ∈ (boxPQ (pbox x₀ Xt) Xz n).1.toSet :=
  (mem_boxPQ x₀ Xt Xz n hz ht).1

theorem mem_boxQ (x₀ : Dya) (Xt : IV) (Xz : CBox) (n : ℕ) {z : ℂ} {t : ℝ}
    (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    q x₀.toReal n (mkE z t) ∈ (boxPQ (pbox x₀ Xt) Xz n).2.toSet :=
  (mem_boxPQ x₀ Xt Xz n hz ht).2

theorem mem_boxS (x₀ : Dya) (Xt : IV) (Xz : CBox) (n : ℕ) {z : ℂ} {t : ℝ}
    (hz : z ∈ Xz.toSet) (ht : t ∈ Xt.toSet) :
    ss x₀.toReal n (mkE z t) ∈ (boxS (pbox x₀ Xt) Xz n).toSet := by
  induction n with
  | zero => simp [boxS]
  | succ n ih =>
    have hV := mem_boxV x₀ Xt Xz n hz ht
    have h2 : (2 : ℂ) * star (Z x₀.toReal n (mkE z t)) ∈
        (((boxV (pbox x₀ Xt) Xz n).conj).mulScalar Dya.two).toSet := by
      have := CBox.mem_mulScalar (B := (boxV (pbox x₀ Xt) Xz n).conj)
        (CBox.mem_conj hV) (a := Dya.two)
      simpa [Dya.toReal_two] using this
    have h := Work.SeedCertNum.CBox_mem_mul h2 (CBox.mem_conj ih)
    have hI : Complex.I ∈ boxCI.toSet := by
      refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [boxCI, Dya.toReal_zero, Dya.toReal_one]
    have := CBox.mem_add hI h
    simpa [boxS, ss_succ] using this

end

end Work.SeedCert
