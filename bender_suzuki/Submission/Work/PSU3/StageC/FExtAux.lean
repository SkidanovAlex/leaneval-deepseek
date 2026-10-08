/-
# `Work.PSU3.StageC.FExtAux` — model lemmas for `f_formula_extension`

Helper lemmas for the proof of `Work.PSU3.StageC.f_formula_extension` (Peterfalvi II
Ch. VII §3 (5), the propagation of the formula `f(x,y) = (x/y, 1/y)` from `Q₀` and one
coset `pQ₀` to all of `Q`).

Contents:

* `zel u hu` — the element `⟨0,u⟩` of `SZ E` for `u` fixed by `σE`;
* `sunit a` — the unit `σE a`;
* `fMapTot_invol` — `fMapTot` is an involution;
* `fMapTot_torusAct` (Lemma N) — `fMapTot (torusAct a z) = torusAct (σE a)⁻¹ (fMapTot z)`,
  the model identity behind the `KW`-equivariance of `fcan`;
* `torusAct_fMapTot_zel` (Lemma M) — the model identity behind the recursion (2) of §2
  along a `Q₀`-coset;
* `exists_v_div_line` — the arithmetic fact that the family `{w/(β+v) : v ∈ F}` meets
  every `F*`-line of `E*` other than the line of `w`, which is what makes the coset
  argument cover all of `Q`.
-/
import Mathlib
import Submission.Work.PSU3.StageC.FSuz
import Submission.Work.PSU3.FMap.torusAct_mul
import Submission.Work.PSU3.FMap.torusAct_bijective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Work.PSU3

namespace Work.PSU3.StageC

variable {L : Type*} [Field L] [FrobeniusInvolution L] [CharP L 2]

/-- `⟨0,u⟩ ∈ SZ L` for `u` fixed by `σE`. -/
def zel (u : L) (hu : σE u = u) : SZ L := ⟨0, u, by rw [hu, CharTwo.add_self_eq_zero, zero_mul]⟩

@[simp] lemma zel_x (u : L) (hu : σE u = u) : (zel u hu).x = 0 := rfl
@[simp] lemma zel_y (u : L) (hu : σE u = u) : (zel u hu).y = u := rfl

lemma zel_mul_self (u : L) (hu : σE u = u) : zel u hu * zel u hu = 1 := by
  ext <;> simp [zel, CharTwo.add_self_eq_zero]

/-- The unit `σE a`. -/
def sunit (a : Lˣ) : Lˣ := Units.map (σE.toMonoidHom) a

@[simp] lemma sunit_val (a : Lˣ) : ((sunit a : Lˣ) : L) = σE (a : L) := by
  simp [sunit]

@[simp] lemma sunit_inv_val (a : Lˣ) : (((sunit a)⁻¹ : Lˣ) : L) = (σE (a : L))⁻¹ := by
  simp [sunit]

lemma torusAct_one (a : Lˣ) : SZ.torusAct a (1 : SZ L) = 1 := by
  apply SZ.ext <;> simp [SZ.torusAct]

/-- `fMapTot` preserves `≠ 1`. -/
theorem fMapTot_ne_one {z : SZ L} (hz : z ≠ 1) : fMapTot z ≠ 1 := by
  rw [fMapTot_of_ne_one hz]
  intro h
  have hy : (SZ.fMap z hz).y = 0 := by rw [h]; rfl
  rw [SZ.fMap_y] at hy
  exact (SZ.y_ne_zero_of_ne_one hz) (inv_eq_zero.mp hy)

/-- `fMapTot` is an involution. -/
theorem fMapTot_invol (z : SZ L) : fMapTot (fMapTot z) = z := by
  rcases eq_or_ne z 1 with rfl | hz
  · rw [fMapTot_one, fMapTot_one]
  · have e1 : fMapTot z = SZ.fMap z hz := fMapTot_of_ne_one hz
    have hfm : SZ.fMap z hz ≠ 1 := by rw [← e1]; exact fMapTot_ne_one hz
    rw [e1, fMapTot_of_ne_one hfm]
    exact Work.PSU3.FMap.fMap_invol z hz hfm

/-- **Lemma N**: `fMapTot ∘ torusAct a = torusAct ((σE a)⁻¹) ∘ fMapTot`. -/
theorem fMapTot_torusAct (a : Lˣ) (z : SZ L) :
    fMapTot (SZ.torusAct a z) = SZ.torusAct (sunit a)⁻¹ (fMapTot z) := by
  rcases eq_or_ne z 1 with rfl | hz
  · rw [torusAct_one, fMapTot_one, torusAct_one]
  · have ht : SZ.torusAct a z ≠ 1 := by
      intro h
      apply hz
      have hinj : Function.Injective (SZ.torusAct a) :=
        (Work.PSU3.FMap.torusAct_bijective a).1
      exact hinj (by rw [h, torusAct_one])
    have hy : z.y ≠ 0 := SZ.y_ne_zero_of_ne_one hz
    rw [fMapTot_of_ne_one ht, fMapTot_of_ne_one hz]
    apply SZ.ext
    · simp only [SZ.fMap_x, SZ.torusAct_x, SZ.torusAct_y, sunit_inv_val]
      have ha : (a : L) ≠ 0 := Units.ne_zero a
      have hsa : σE (a : L) ≠ 0 := fun h => ha (σE.injective (by rw [h, map_zero]))
      field_simp
    · simp only [SZ.fMap_y, SZ.torusAct_x, SZ.torusAct_y, sunit_inv_val, map_mul,
        σE_inv, σE_σE]
      have ha : (a : L) ≠ 0 := Units.ne_zero a
      have hsa : σE (a : L) ≠ 0 := fun h => ha (σE.injective (by rw [h, map_zero]))
      field_simp

/-- In characteristic two, `1 + x (1+x)⁻¹ = (1+x)⁻¹`. -/
lemma one_add_mul_inv (x : L) (hx : (1 : L) + x ≠ 0) :
    (1 : L) + x * (1 + x)⁻¹ = (1 + x)⁻¹ := by
  have key : (1 + x) * (1 + x * (1 + x)⁻¹) = 1 := by
    rw [mul_add, mul_one, mul_comm x (1 + x)⁻¹, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  have h2 := eq_inv_of_mul_eq_one_right key
  rw [h2]

/-- In characteristic two, `a² (y⁻¹ + a)⁻¹ + a = (y + a⁻¹)⁻¹`. -/
lemma char2_aux (y a : L) (ha : a ≠ 0) (hy : y ≠ 0) (hd : 1 + y * a ≠ 0) :
    a * a * (y⁻¹ + a)⁻¹ + a = (y + a⁻¹)⁻¹ := by
  have h1 : y⁻¹ + a ≠ 0 := by
    intro h
    apply hd
    have hm : y * (y⁻¹ + a) = 1 + y * a := by rw [mul_add, mul_inv_cancel₀ hy]
    rw [h, mul_zero] at hm
    exact hm.symm
  have h2 : y + a⁻¹ ≠ 0 := by
    intro h
    apply hd
    have hm : (y + a⁻¹) * a = y * a + 1 := by rw [add_mul, inv_mul_cancel₀ ha]
    rw [h, zero_mul] at hm
    simpa [add_comm] using hm.symm
  field_simp
  ring_nf
  exact one_add_mul_inv (a * y) (by rw [mul_comm a y]; exact hd)

/-- **Lemma M**: the model identity behind the §2(2) recursion along a `Q₀`-coset.
For `z ∉ Q₀` and `a ∈ F*`,
`torusAct a (f (f z · zel a)) · zel a = f (z · zel a⁻¹)`. -/
theorem torusAct_fMapTot_zel (z : SZ L) (hz : z.x ≠ 0)
    (a : Lˣ) (ha : σE (a : L) = (a : L)) :
    SZ.torusAct a (fMapTot (fMapTot z * zel (a : L) ha)) * zel (a : L) ha =
      fMapTot (z * zel ((a : L)⁻¹) (by rw [map_inv₀, ha])) := by
  have hz1 : z ≠ 1 := fun h => hz (by rw [h]; rfl)
  have hz1' : z * zel ((a : L)⁻¹) (by rw [map_inv₀, ha]) ≠ 1 := by
    intro h
    have hx : (z * zel ((a : L)⁻¹) (by rw [map_inv₀, ha])).x = 0 := by rw [h]; rfl
    rw [SZ.mul_x, zel_x, add_zero] at hx
    exact hz hx
  have hyz : z.y ≠ 0 := SZ.y_ne_zero_of_ne_one hz1
  have hm1 : fMapTot z * zel (a : L) ha ≠ 1 := by
    intro h
    have hx : (fMapTot z * zel (a : L) ha).x = 0 := by rw [h]; rfl
    rw [SZ.mul_x, zel_x, add_zero, fMapTot_of_ne_one hz1, SZ.fMap_x] at hx
    rcases div_eq_zero_iff.mp hx with h1 | h1
    · exact hz h1
    · exact absurd h1 hyz
  have e1 : fMapTot z = SZ.fMap z hz1 := fMapTot_of_ne_one hz1
  have h1 : SZ.fMap z hz1 * zel (a : L) ha ≠ 1 := by rw [← e1]; exact hm1
  refine Eq.trans ?_ (fMapTot_of_ne_one
    (p := z * zel ((a : L)⁻¹) (by rw [map_inv₀, ha])) hz1').symm
  calc SZ.torusAct a (fMapTot (fMapTot z * zel (a : L) ha)) * zel (a : L) ha
      = SZ.torusAct a (fMapTot (SZ.fMap z hz1 * zel (a : L) ha)) * zel (a : L) ha := by
          rw [e1]
    _ = SZ.torusAct a (SZ.fMap (SZ.fMap z hz1 * zel (a : L) ha) h1) * zel (a : L) ha := by
          rw [fMapTot_of_ne_one h1]
    _ = SZ.fMap (z * zel ((a : L)⁻¹) (by rw [map_inv₀, ha])) hz1' := by
          apply SZ.ext
          · simp only [SZ.fMap_x, SZ.fMap_y, SZ.torusAct_x, SZ.torusAct_y, SZ.mul_x, SZ.mul_y,
              zel_x, zel_y, map_zero, add_zero, mul_zero, zero_mul, σE_mul]
            have hzy : z.y ≠ 0 := SZ.y_ne_zero_of_ne_one hz1
            have ha0 : (a : L) ≠ 0 := Units.ne_zero a
            field_simp
            ring_nf
          · simp only [SZ.fMap_x, SZ.fMap_y, SZ.torusAct_x, SZ.torusAct_y, SZ.mul_x, SZ.mul_y,
              zel_x, zel_y, map_zero, add_zero, mul_zero, zero_mul, σE_mul]
            rw [ha]
            have hd : (1 + z.y * (a : L)) ≠ 0 := by
              intro hc
              have hzya : z.y = (a : L)⁻¹ := by
                have h2 : z.y * (a : L) = 1 := by
                  have h3 := eq_neg_of_add_eq_zero_left hc
                  rw [CharTwo.neg_eq] at h3
                  exact h3.symm
                exact eq_inv_of_mul_eq_one_left h2
              have hsq : z.x * σE z.x = 0 := by
                have hherm := z.herm
                rw [hzya, map_inv₀, ha, CharTwo.add_self_eq_zero] at hherm
                exact hherm.symm
              rcases mul_eq_zero.mp hsq with h1 | h1
              · exact hz h1
              · exact hz (σE.injective (by rw [h1, map_zero]))
            exact char2_aux z.y (a : L) (Units.ne_zero a) hyz hd

/-- **The arithmetic core of the coset argument.**  For `w, μ ≠ 0`, `β` with
`β + σE β = (μ σE μ)(w σE w)` (so `β ∉ F`), and `c' ≠ 0` with `w/c' ∉ F*` (encoded by
`w σE c' + σE w c' ≠ 0`), there is `v ∈ F` with `w/(β+v)` lying on the `F*`-line of `c'`. -/
theorem exists_v_div_line {n : ℕ} (w β μ : E n) (hw : w ≠ 0) (hμ : μ ≠ 0)
    (htr : β + σE β = (μ * σE μ) * (w * σE w))
    (c' : E n) (hc' : c' ≠ 0)
    (hline : w * σE c' + σE w * c' ≠ 0) :
    ∃ v : E n, σE v = v ∧
      ∃ f₀ : E n, σE f₀ = f₀ ∧ f₀ ≠ 0 ∧ w / (β + v) = f₀ * c' := by
  have hσ0 : ∀ x : E n, x ≠ 0 → σE x ≠ 0 := fun x hx h => hx (σE.injective (by rw [h, map_zero]))
  set A : E n := w * σE c' + σE w * c' with hA
  have hA0 : A ≠ 0 := hline
  set tr : E n := β + σE β with htr_eq
  have htr0 : tr ≠ 0 := by
    rw [htr]
    exact mul_ne_zero (mul_ne_zero hμ (hσ0 μ hμ)) (mul_ne_zero hw (hσ0 w hw))
  set y : E n := w * σE c' * tr / A with hy
  have hy0 : y ≠ 0 := by
    rw [hy]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero hw (hσ0 c' hc')) htr0) hA0
  have hσA : σE A = A := by
    rw [hA]; simp only [map_add, map_mul, σE_σE]; ring
  have hσtr : σE tr = tr := by
    rw [htr_eq]; simp only [map_add, σE_σE]; ring
  have hyσ : y + σE y = tr := by
    rw [hy, map_div₀, hσA]
    simp only [map_mul, σE_σE]
    rw [hσtr]
    field_simp
    try rw [hA]; try ring
  refine ⟨y + β, ?_, A / (c' * σE c' * tr), ?_, ?_, ?_⟩
  · -- `σE v = v`
    have hv : (y + β) + σE (y + β) = 0 := by
      rw [map_add]
      have h0 : y + σE y + (β + σE β) = 0 := by
        rw [hyσ, htr_eq, CharTwo.add_self_eq_zero]
      rw [← h0]; ring
    have hv' := eq_neg_of_add_eq_zero_left hv
    rw [CharTwo.neg_eq] at hv'
    exact hv'.symm
  · -- `σE f₀ = f₀`
    rw [map_div₀]
    simp only [hσA, hσtr, map_mul, σE_σE]
    congr 1
    ring
  · -- `f₀ ≠ 0`
    exact div_ne_zero hA0 (mul_ne_zero (mul_ne_zero hc' (hσ0 c' hc')) htr0)
  · -- the equality
    have hβv : β + (y + β) = y := by
      rw [← add_assoc, add_comm β y, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    rw [hβv, hy]
    field_simp
    try ring

end Work.PSU3.StageC
