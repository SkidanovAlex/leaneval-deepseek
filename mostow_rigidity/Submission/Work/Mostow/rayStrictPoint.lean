import Mathlib
import Submission.Work.Mostow.KMdefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BoostTransitive
import Submission.Work.Mostow.mink_expand
import Submission.Work.Mostow.mink_hlift_neg_cosh

/-!
# `rayStrictPoint`: strictly increasing displacement at a nearby point

`rayStrictPoint n hA hI y x` : for every `τ > 0` there is `x'` with `hdist x x' < τ` such that
*every* isometry `g` fixing the point `y` and with `0 < hdist x (g • x)` satisfies
`hdist x (g • x) < hdist x' (g • x')`.  This is statement (i) ("point case") of KM-E in the
Kazhdan–Margulis chapter: the displacement at the *single* point `x'` strictly dominates the
displacement at `x`, simultaneously for all such `g`, and `x'` may be taken arbitrarily close
to `x`.

## Proof

By transitivity of the `PO n 1`-action (`BoostTransitive`) it suffices to treat `y = 0`,
and then `g` fixes `0`; this is `rayStrictPoint_zero`.  There, after the trivial case `x = 0`,
one works in the hyperboloid model (`Submission.Mostow.Hyper`):

* `Y = hlift 0` is future unit timelike, `X = hlift x` lies on the sheet, and
  `X = cosh r • Y + sinh r • V` with `r = hdist 0 x` and `V` the unit spacelike vector
  orthogonal to `Y` along the geodesic ray from `0` through `x` (so `⟨V,V⟩ = 1`, `⟨Y,V⟩ = 0`).
* For `g` fixing `0`, the linear part `M = tsign (rep g) • mat (rep g)` preserves the Minkowski
  form and fixes `Y`, hence `W = M V` is again unit spacelike orthogonal to `Y`, and
  `cosh (hdist x (g • x)) = 1 + sinh² r * (1 - ⟨V,W⟩)`.
* The hypothesis `hdist x (g • x) > 0` forces `⟨V,W⟩ < 1`.  For the nearby point `X'` at
  geodesic parameter `r + δ` (`δ = τ/2`) the same computation gives
  `cosh (hdist x' (g • x')) = 1 + sinh²(r + δ) * (1 - ⟨V,W⟩) > 1 + sinh² r * (1 - ⟨V,W⟩)`,
  and `cosh` is strictly increasing on `[0, ∞)`.  Also `hdist x x' = δ < τ`.

The main algebraic inputs are `mink_expand` and `mink_hlift_neg_cosh` (delegated, in
`Submission.Work.Mostow.mink_expand` / `mink_hlift_neg_cosh`) together with the bilinearity of
the Minkowski form proved in the `RSP` namespace below.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

namespace RSP

variable {n : ℕ}

/-! ## Bilinearity of the Minkowski form `Submission.Mostow.Hyper.mink` -/

lemma mink_add_left (x y z : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink (x + y) z = Hyper.mink x z + Hyper.mink y z := by
  simp only [Hyper.mink_apply, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

lemma mink_add_right (x y z : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink x (y + z) = Hyper.mink x y + Hyper.mink x z := by
  simp only [Hyper.mink_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

lemma mink_neg_left (x y : Fin n ⊕ Fin 1 → ℝ) : Hyper.mink (-x) y = - Hyper.mink x y := by
  simp only [Hyper.mink_apply, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
  ring

lemma mink_neg_right (x y : Fin n ⊕ Fin 1 → ℝ) : Hyper.mink x (-y) = - Hyper.mink x y := by
  simp only [Hyper.mink_apply, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
  ring

lemma mink_sub_left (x y z : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink (x - y) z = Hyper.mink x z - Hyper.mink y z := by
  rw [sub_eq_add_neg, mink_add_left, mink_neg_left]; ring

lemma mink_sub_right (x y z : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink x (y - z) = Hyper.mink x y - Hyper.mink x z := by
  rw [sub_eq_add_neg, mink_add_right, mink_neg_right]; ring

lemma mink_smul_left (c : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink (c • x) y = c * Hyper.mink x y := by
  simpa using Hyper.mink_smul c 1 x y

lemma mink_smul_right (c : ℝ) (x y : Fin n ⊕ Fin 1 → ℝ) :
    Hyper.mink x (c • y) = c * Hyper.mink x y := by
  simpa using Hyper.mink_smul 1 c x y

lemma mink_comm (x y : Fin n ⊕ Fin 1 → ℝ) : Hyper.mink x y = Hyper.mink y x := by
  simp only [Hyper.mink_apply]
  rw [Finset.sum_congr rfl (fun i _ => mul_comm (x (Sum.inl i)) (y (Sum.inl i)))]
  ring

lemma mink_quad (Y V W : Fin n ⊕ Fin 1 → ℝ) (c s : ℝ)
    (hYY : Hyper.mink Y Y = -1) (hYW : Hyper.mink Y W = 0) (hVY : Hyper.mink V Y = 0) :
    Hyper.mink (c • Y + s • V) (c • Y + s • W) = -(c ^ 2) + s ^ 2 * Hyper.mink V W := by
  rw [mink_expand, hYY, hYW, hVY]
  ring

lemma mink_self_sub (X Y : Fin n ⊕ Fin 1 → ℝ) (a : ℝ) :
    Hyper.mink (X - a • Y) (X - a • Y)
      = Hyper.mink X X - 2 * a * Hyper.mink X Y + a ^ 2 * Hyper.mink Y Y := by
  simp only [sub_eq_add_neg, mink_add_left, mink_add_right, mink_neg_left, mink_neg_right,
    mink_smul_left, mink_smul_right]
  rw [mink_comm Y X]
  ring

/-- The Minkowski pairing of the two points at parameters `r` and `r + δ` on a geodesic ray. -/
lemma mink_ray (Y V : Fin n ⊕ Fin 1 → ℝ) (r δ : ℝ)
    (hYY : Hyper.mink Y Y = -1) (hYV : Hyper.mink Y V = 0) (hVY : Hyper.mink V Y = 0)
    (hVV : Hyper.mink V V = 1) :
    Hyper.mink (Real.cosh r • Y + Real.sinh r • V) (Real.cosh (r + δ) • Y + Real.sinh (r + δ) • V)
      = -Real.cosh δ := by
  simp only [mink_add_left, mink_add_right, mink_smul_left, mink_smul_right]
  rw [hYY, hYV, hVY, hVV]
  have hcs : Real.cosh δ = Real.cosh (r + δ) * Real.cosh r - Real.sinh (r + δ) * Real.sinh r := by
    have h := Real.cosh_sub (r + δ) r
    rwa [show r + δ - r = δ from by ring] at h
  rw [hcs]; ring

/-! ## The cosh-kernel and the Minkowski pairing of two lifted points -/

/-- The sheet lemma: the lift of `g • u` is the matrix of `g` applied to the lift of `u`. -/
lemma hlift_smul_rep (_hA : POActionProp n) (g : PO n 1) (u : E n) :
    hlift (g • u) = Matrix.mulVec (tsign (rep g) • mat (rep g)) (hlift u) := by
  have h : g • u = actO (rep g) u := rfl
  rw [h, Hyper.hlift_actO, Matrix.smul_mulVec]

end RSP

open RSP

/-- The base-point (`y = 0`) case of `rayStrictPoint`. -/
theorem rayStrictPoint_zero (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) (x : E n) :
    ∀ τ : ℝ, 0 < τ → ∃ x' : E n, hdist x x' < τ ∧
      ∀ g : PO n 1, g • (0 : E n) = 0 → 0 < hdist x (g • x) →
        hdist x (g • x) < hdist x' (g • x') := by
  intro τ hτ
  let d := HypIsoData.ofProp hI
  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨0, ?_, ?_⟩
    · have h : hdist (0 : E n) 0 = 0 := (d.eq_zero 0 0).2 rfl
      rw [h]; exact hτ
    · intro g hg hpos
      exfalso
      have h : hdist (0 : E n) (g • 0) = 0 := by rw [hg, (d.eq_zero 0 0).2 rfl]
      rw [h] at hpos
      exact lt_irrefl 0 hpos
  · set r : ℝ := hdist 0 x with hrdef
    have hrpos : 0 < r := by
      rw [hrdef]
      refine lt_of_le_of_ne (d.nonneg 0 x) (fun h => hx0 ?_)
      exact ((d.eq_zero 0 x).1 h.symm).symm
    have hsinhne : Real.sinh r ≠ 0 := fun h => hrpos.ne' (Real.sinh_eq_zero.mp h)
    have hsinhpos : 0 < Real.sinh r := Real.sinh_pos_iff.mpr hrpos
    set Y : Fin n ⊕ Fin 1 → ℝ := hlift (0 : E n) with hYdef
    set X : Fin n ⊕ Fin 1 → ℝ := hlift x with hXdef
    have hYY : Hyper.mink Y Y = -1 := by rw [hYdef]; exact Hyper.mink_hlift_self 0
    have hXX : Hyper.mink X X = -1 := by rw [hXdef]; exact Hyper.mink_hlift_self x
    have hXY : Hyper.mink X Y = -Real.cosh r := by
      have h := mink_hlift_neg_cosh x (0 : E n)
      rw [← hXdef, ← hYdef, d.symm x 0, ← hrdef] at h
      exact h
    set V : Fin n ⊕ Fin 1 → ℝ := (Real.sinh r)⁻¹ • (X - Real.cosh r • Y) with hVdef
    have hYV : Hyper.mink Y V = 0 := by
      rw [hVdef, mink_smul_right, mink_sub_right, mink_smul_right, ← mink_comm X Y, hXY, hYY]
      ring
    have hVY : Hyper.mink V Y = 0 := by
      rw [hVdef, mink_smul_left, mink_sub_left, mink_smul_left, hXY, hYY]
      ring
    have hVV : Hyper.mink V V = 1 := by
      have h1 : Hyper.mink V V
          = ((Real.sinh r)⁻¹) ^ 2
              * Hyper.mink (X - Real.cosh r • Y) (X - Real.cosh r • Y) := by
        rw [hVdef, mink_smul_left, mink_smul_right]; ring
      rw [h1, mink_self_sub, hXX, hXY, hYY]
      rw [show (-1 - 2 * Real.cosh r * (-Real.cosh r) + Real.cosh r ^ 2 * (-1))
            = Real.sinh r ^ 2 from by nlinarith [Real.cosh_sq_sub_sinh_sq r]]
      rw [← mul_pow, inv_mul_cancel₀ hsinhne, one_pow]
    have hXdecomp : X = Real.cosh r • Y + Real.sinh r • V := by
      have h : Real.sinh r • V = X - Real.cosh r • Y := by
        rw [hVdef, smul_smul, mul_inv_cancel₀ hsinhne, one_smul]
      rw [h]
      abel
    set δ : ℝ := τ / 2 with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; linarith
    have hδτ : δ < τ := by rw [hδdef]; linarith
    have hsinhlt : Real.sinh r ^ 2 < Real.sinh (r + δ) ^ 2 := by
      have h1 : Real.sinh r < Real.sinh (r + δ) := Real.sinh_lt_sinh.mpr (by linarith)
      have h0 : 0 ≤ Real.sinh r := le_of_lt hsinhpos
      simpa [pow_two] using mul_self_lt_mul_self h0 h1
    set X' : Fin n ⊕ Fin 1 → ℝ := Real.cosh (r + δ) • Y + Real.sinh (r + δ) • V with hX'def
    have hX'neg : Hyper.mink X' X' = -1 := by
      rw [hX'def, mink_quad Y V V (Real.cosh (r + δ)) (Real.sinh (r + δ)) hYY hYV hVY, hVV]
      have hcs := Real.cosh_sq_sub_sinh_sq (r + δ)
      linarith
    have hVtime : V (Sum.inr 0) = 0 := by
      have h : Hyper.mink V Y = - V (Sum.inr 0) := by
        rw [hYdef, Hyper.mink_apply]
        simp [hlift, tpart]
      rw [hVY] at h
      linarith
    have hYtime : Y (Sum.inr 0) = 1 := by rw [hYdef]; simp [hlift, tpart]
    have hX'time : 0 < X' (Sum.inr 0) := by
      rw [hX'def]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hYtime, hVtime, mul_zero, add_zero, mul_one]
      exact Real.cosh_pos _
    have hhlift : hlift (Hyper.spat X') = X' := Hyper.hlift_spat_of_mink X' hX'neg hX'time
    refine ⟨Hyper.spat X', ?_, ?_⟩
    · have hXX' : Hyper.mink X X' = -Real.cosh δ := by
        rw [hXdecomp, hX'def]
        exact mink_ray Y V r δ hYY hYV hVY hVV
      have hx'cosh : Real.cosh (hdist x (Hyper.spat X')) = Real.cosh δ := by
        have h1 := mink_hlift_neg_cosh x (Hyper.spat X')
        rw [← hXdef, hhlift, hXX'] at h1
        linarith
      have hd_eq : hdist x (Hyper.spat X') = δ :=
        Real.cosh_injOn (Set.mem_Ici.mpr (d.nonneg x _))
          (Set.mem_Ici.mpr (le_of_lt hδpos)) hx'cosh
      rw [hd_eq]; exact hδτ
    · intro g hg0 hpos
      set M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ := tsign (rep g) • mat (rep g) with hMdef
      have hMhlift : ∀ u : E n, hlift (g • u) = Matrix.mulVec M (hlift u) := by
        intro u
        rw [hlift_smul_rep hA g u, ← hMdef]
      have hMY : Matrix.mulVec M Y = Y := by
        have h := hMhlift (0 : E n)
        rw [hg0, ← hYdef] at h
        exact h.symm
      have hMform : ∀ a b : Fin n ⊕ Fin 1 → ℝ,
          Hyper.mink (Matrix.mulVec M a) (Matrix.mulVec M b) = Hyper.mink a b := by
        intro a b
        rw [hMdef, Matrix.smul_mulVec, Matrix.smul_mulVec, Hyper.mink_smul,
            Hyper.tsign_mul_self, one_mul]
        exact Hyper.mink_mulVec (mat (rep g)) (Hyper.mat_conj (rep g)) a b
      set W : Fin n ⊕ Fin 1 → ℝ := Matrix.mulVec M V with hWdef
      have hWY : Hyper.mink W Y = 0 := by
        have h := hMform V Y
        rw [← hWdef, hMY, hVY] at h
        exact h
      have hYW : Hyper.mink Y W = 0 := by rw [mink_comm]; exact hWY
      have hAid : Real.cosh (hdist x (g • x)) = 1 + Real.sinh r ^ 2 * (1 - Hyper.mink V W) := by
        have h1 := mink_hlift_neg_cosh x (g • x)
        rw [hMhlift x, ← hXdef] at h1
        have hMX : Matrix.mulVec M X = Real.cosh r • Y + Real.sinh r • W := by
          rw [hXdecomp, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hMY, ← hWdef]
        have hval : Hyper.mink X (Matrix.mulVec M X)
            = -(Real.cosh r ^ 2) + Real.sinh r ^ 2 * Hyper.mink V W := by
          rw [hMX, hXdecomp, mink_quad Y V W (Real.cosh r) (Real.sinh r) hYY hYW hVY]
        rw [hval] at h1
        have hcs := Real.cosh_sq_sub_sinh_sq r
        linarith
      have hc0 : 0 < 1 - Hyper.mink V W := by
        have hlt : 1 < Real.cosh (hdist x (g • x)) := Real.one_lt_cosh.mpr (ne_of_gt hpos)
        rw [hAid] at hlt
        have hs2 : 0 < Real.sinh r ^ 2 := pow_pos hsinhpos 2
        have h : 0 < Real.sinh r ^ 2 * (1 - Hyper.mink V W) := by linarith
        exact pos_of_mul_pos_right h (le_of_lt hs2)
      have hBid : Real.cosh (hdist (Hyper.spat X') (g • Hyper.spat X'))
          = 1 + Real.sinh (r + δ) ^ 2 * (1 - Hyper.mink V W) := by
        have h1 := mink_hlift_neg_cosh (Hyper.spat X') (g • Hyper.spat X')
        rw [hMhlift (Hyper.spat X'), hhlift] at h1
        have hMX' : Matrix.mulVec M X' = Real.cosh (r + δ) • Y + Real.sinh (r + δ) • W := by
          rw [hX'def, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hMY, ← hWdef]
        have hval : Hyper.mink X' (Matrix.mulVec M X')
            = -(Real.cosh (r + δ) ^ 2) + Real.sinh (r + δ) ^ 2 * Hyper.mink V W := by
          rw [hMX', hX'def, mink_quad Y V W (Real.cosh (r + δ)) (Real.sinh (r + δ)) hYY hYW hVY]
        rw [hval] at h1
        have hcs := Real.cosh_sq_sub_sinh_sq (r + δ)
        linarith
      have hcoshlt : Real.cosh (hdist x (g • x))
          < Real.cosh (hdist (Hyper.spat X') (g • Hyper.spat X')) := by
        rw [hAid, hBid]
        have hh := mul_lt_mul_of_pos_right hsinhlt hc0
        linarith
      have hfin := Real.cosh_lt_cosh.mp hcoshlt
      rw [abs_of_nonneg (d.nonneg x (g • x)),
          abs_of_nonneg (d.nonneg (Hyper.spat X') (g • Hyper.spat X'))] at hfin
      exact hfin

theorem rayStrictPoint (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n) (y x : E n) :
    ∀ τ : ℝ, 0 < τ → ∃ x' : E n, hdist x x' < τ ∧
      ∀ g : PO n 1, g • y = y → 0 < hdist x (g • x) → hdist x (g • x) < hdist x' (g • x') := by
  intro τ hτ
  let d := HypIsoData.ofProp hI
  let p := POBasic.ofProp hA
  obtain ⟨h, hh⟩ := (BoostTransitive n hA).2 y 0
  obtain ⟨xb, hxbτ, hxbprop⟩ := rayStrictPoint_zero n hA hI (h • x) τ hτ
  have h1 : h • (h⁻¹ • xb) = xb := by
    rw [← p.mul_smul, mul_inv_cancel, p.one_smul]
  refine ⟨h⁻¹ • xb, ?_, ?_⟩
  · rw [← d.isom_smul h x (h⁻¹ • xb), h1]
    exact hxbτ
  · intro g hgy hpos
    set g' : PO n 1 := h * g * h⁻¹ with hg'def
    have hinv0 : h⁻¹ • (0 : E n) = y := by
      rw [← hh, ← p.mul_smul, inv_mul_cancel, p.one_smul]
    have hg'0 : g' • (0 : E n) = 0 := by
      rw [hg'def, p.mul_smul, p.mul_smul, hinv0, hgy, hh]
    have h2x : h⁻¹ • (h • x) = x := by
      rw [← p.mul_smul, inv_mul_cancel, p.one_smul]
    have hg'x : g' • (h • x) = h • (g • x) := by
      rw [hg'def, p.mul_smul, p.mul_smul, h2x]
    have hpos' : 0 < hdist (h • x) (g' • (h • x)) := by
      rw [hg'x, d.isom_smul]
      exact hpos
    have hkey := hxbprop g' hg'0 hpos'
    have hleft : hdist x (g • x) = hdist (h • x) (g' • (h • x)) := by
      rw [hg'x, d.isom_smul]
    have hright : hdist (h⁻¹ • xb) (g • (h⁻¹ • xb)) = hdist xb (g' • xb) := by
      have h3 : h • (g • (h⁻¹ • xb)) = g' • xb := by
        rw [hg'def, p.mul_smul, p.mul_smul]
      rw [← d.isom_smul h (h⁻¹ • xb) (g • (h⁻¹ • xb)), h1, h3]
    rw [hleft, hright]
    exact hkey

end Work.Mostow
