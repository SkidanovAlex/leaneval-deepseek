/-
# `Work.PSU3.StageC.FSuz` — the coordinate machinery for `f_formula_of_omega`

Setup common to the Stage C computation `f(ω x) = f(x)` of Peterfalvi II, Ch. VII §3:
the total canonical maps `fcan, gcan, hcan` of `Work.PSU3.StageB.Canon` are used, `zcQ v`
denotes the element `zc v ∈ Q₀`, and we record

* §2(1): `f(zc v) = g(zc v) = zc v⁻¹` and `h(zc v) = a_v` (the `KW`-element with `κ a_v = v`);
* the two recursions coming from H6
  * `f(x zc v) = a_v^{-t} f(f(x) zc v⁻¹) a_v^t zc v⁻¹`  ((2) of §2),
  * `f(zc v x) = h(x)^{-t} f(zc v⁻¹ g(x)) h(x)^t f(x)`  ((3) of §2).
-/
import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField
import Submission.Work.PSU3.GaloisField.fixedField_card
import Submission.Work.PSU3.FMap
import Submission.Work.PSU3.FMap.fMap_invol
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.RankOneUniqueness.canon_exists
import Submission.Work.RankOneUniqueness.canon_unique
import Submission.Work.RankOneUniqueness.f_exists
import Submission.Work.RankOneUniqueness.f_unique
import Submission.Work.PSU3.RankOne.H16
import Submission.Work.PSU3.RankOne.canon_conj
import Submission.Work.PSU3.RankOne.canon_mul
import Submission.Work.PSU3.RankOne.canon_mul_ne_one
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageC.e_zc_eq

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
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.PSU3.StageB

namespace Work.PSU3.StageC

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- The involution `t` satisfies `t * t = 1`. -/
theorem t_mul_self (hS : Work.PSU3.PSU3Hyp H Q t) : t * t = 1 :=
  Work.RankOneUniqueness.mul_self_eq_one hS.split

theorem t_inv (hS : Work.PSU3.PSU3Hyp H Q t) : t⁻¹ = t :=
  Work.RankOneUniqueness.inv_eq_self hS.split

/-- The `Q`-element `zc v` attached to an element of the fixed field. -/
noncomputable def zcQ (fr : Work.PSU3.CoarseFrame H Q t n) (v : Work.PSU3.E n)
    (hv : σE v = v) : Q :=
  ⟨fr.zc v, fr.Q0_le (fr.zc_mem v hv)⟩

@[simp] theorem zcQ_coe (fr : Work.PSU3.CoarseFrame H Q t n) (v : Work.PSU3.E n)
    (hv : σE v = v) : ((zcQ fr v hv : Q) : G) = fr.zc v := rfl

/-- The distinguished involution `s = zc 1` as an element of `Q`. -/
noncomputable def sQ (fr : Work.PSU3.CoarseFrame H Q t n) : Q := ⟨fr.zc 1, fr.Q0_le (fr.zc_mem 1 (by simp))⟩

@[simp] theorem sQ_coe (fr : Work.PSU3.CoarseFrame H Q t n) :
    ((sQ fr : Q) : G) = fr.zc 1 := rfl

theorem sQ_eq (fr : Work.PSU3.CoarseFrame H Q t n) :
    sQ fr = zcQ fr 1 (by simp) := rfl

theorem zcQ_mul (fr : Work.PSU3.CoarseFrame H Q t n) (v w : Work.PSU3.E n)
    (hv : σE v = v) (hw : σE w = w) :
    zcQ fr (v + w) (by rw [map_add, hv, hw]) = zcQ fr v hv * zcQ fr w hw := by
  apply Subtype.ext
  show fr.zc (v + w) = fr.zc v * fr.zc w
  exact fr.zc_add v w hv hw

theorem zcQ_ne_one (fr : Work.PSU3.CoarseFrame H Q t n) (v : Work.PSU3.E n)
    (hv : σE v = v) (hv0 : v ≠ 0) : (zcQ fr v hv : Q) ≠ 1 := by
  intro h
  have h1 : fr.zc v = 1 := by simpa using congrArg (fun z : Q => (z : G)) h
  have h2 : fr.zc v = fr.zc 0 := by rw [h1, StageB.zc_zero fr]
  exact hv0 (fr.zc_inj v 0 hv (by simp) h2)

theorem sQ_ne_one (fr : Work.PSU3.CoarseFrame H Q t n) : (sQ fr : Q) ≠ 1 := by
  intro h
  have h1 : fr.zc 1 = (1 : G) := by simpa [sQ] using congrArg (fun z : Q => (z : G)) h
  exact StageB.frameS_ne_one fr (by simpa [StageB.frameS] using h1)

theorem sQ_coe_ne_one (fr : Work.PSU3.CoarseFrame H Q t n) : ((sQ fr : Q) : G) ≠ 1 :=
  fun h => sQ_ne_one fr (Subtype.ext h)

theorem zcQ_coe_ne_one (fr : Work.PSU3.CoarseFrame H Q t n) (v : Work.PSU3.E n)
    (hv : σE v = v) (hv0 : v ≠ 0) : ((zcQ fr v hv : Q) : G) ≠ 1 :=
  fun h => zcQ_ne_one fr v hv hv0 (Subtype.ext h)

/-- Square roots exist in the fixed field of a finite field of characteristic two. -/
theorem exists_sqrt_fixed (v : Work.PSU3.E n) (hv : σE v = v) :
    ∃ b : Work.PSU3.E n, σE b = b ∧ b ^ 2 = v := by
  let Fix := {x : Work.PSU3.E n // σE x = x}
  haveI : Finite Fix := inferInstance
  let φ : Fix → Fix := fun x => ⟨x.1 ^ 2, by rw [map_pow, x.2]⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have hval : a.1 ^ 2 = b.1 ^ 2 := congrArg Subtype.val hab
    have hab' : a.1 = b.1 := by
      have h2 : (a.1 + b.1) * (a.1 + b.1) = 0 := by
        rw [← pow_two, CharTwo.add_sq, hval]
        exact CharTwo.add_self_eq_zero _
      have h3 : a.1 + b.1 = 0 := mul_self_eq_zero.mp h2
      rw [eq_neg_of_add_eq_zero_left h3, CharTwo.neg_eq]
    exact Subtype.ext hab'
  have hsurj : Function.Surjective φ := (Finite.injective_iff_surjective).mp hinj
  obtain ⟨b, hb⟩ := hsurj ⟨v, hv⟩
  exact ⟨b.1, b.2, congrArg Subtype.val hb⟩

/-- `zc v = d⁻¹ · s · d` for a suitable `KW`-element `d` with `(d:G) ∈ Ksub`. -/
theorem zcQ_eq_conj (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (v : Work.PSU3.E n) (hv : σE v = v) (hv0 : v ≠ 0) :
    ∃ (d : fr.KW) (_ : (d : G) ∈ Work.ThmF.Ksub H t),
      (zcQ fr v hv : G) = (d : G)⁻¹ * fr.zc 1 * (d : G) ∧
      ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) *
        ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) = v := by
  obtain ⟨a, ha, ha2⟩ := exists_sqrt_fixed (n := n) v hv
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at ha2; simp at ha2; exact hv0 ha2.symm
  let au : (Work.PSU3.E n)ˣ := Units.mk0 a ha0
  have hau : σE ((au : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) = (au : Work.PSU3.E n) := ha
  obtain ⟨d, hd⟩ := fr.K_surj au hau
  have hdK : (d : G) ∈ Work.ThmF.Ksub H t := (fr.mem_K_iff d).mpr (by rw [hd]; exact hau)
  have hauv : ((au : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) = a := rfl
  refine ⟨d, hdK, ?_, ?_⟩
  · have h := fr.act_zc_K d hdK 1 (by simp)
    have h2 : ((fr.nm (fr.κ d) : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) = v := by
      rw [hd]
      rw [show ((fr.nm au : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
            = ((au : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) ^ 2 from hsq au hau]
      rw [hauv]; exact ha2
    rw [mul_one] at h
    rw [h2] at h
    exact h.symm
  · rw [hd, hauv]; simpa [pow_two] using ha2

/-- §2(1), `d`-form: for `(d:G)⁻¹ s d = zc v`,
`f(zc v) = g(zc v) = (d:G) s (d:G)⁻¹` and `h(zc v) = (d:G)(d:G)`. -/
theorem canon_zcQ_of_conj (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {v : Work.PSU3.E n} (hv : σE v = v) {d : fr.KW} (hdK : (d : G) ∈ Work.ThmF.Ksub H t)
    (hzc : (zcQ fr v hv : G) = (d : G)⁻¹ * fr.zc 1 * (d : G)) :
    (fcan hS.split (zcQ fr v hv) : G) = (d : G) * fr.zc 1 * (d : G)⁻¹ ∧
    (gcan hS.split (zcQ fr v hv) : G) = (d : G) * fr.zc 1 * (d : G)⁻¹ ∧
    (hcan hS.split (zcQ fr v hv) : G) = (d : G) * (d : G) := by
  have htd : t * (d : G) * t = (d : G)⁻¹ := StageB.tconj_eq_inv hS.split fr hdK
  -- canonical data of `s`
  have hcanon_s : t * ((sQ fr : Q) : G) * t =
      ((sQ fr : Q) : G) * (1 : G) * t * ((sQ fr : Q) : G) := by
    show t * fr.zc 1 * t = fr.zc 1 * (1 : G) * t * fr.zc 1
    rw [mul_one]; exact fr.s_struct
  have key_s := Work.PSU3.StageB.canon_unique'' hS.split (sQ_coe_ne_one fr)
    (g := sQ fr) (d := 1) (y := sQ fr) hcanon_s
  have hf_s : (fcan hS.split (sQ fr) : G) = fr.zc 1 := key_s.2.2.symm
  have hg_s : (gcan hS.split (sQ fr) : G) = fr.zc 1 := key_s.1.symm
  have hh_s : (hcan hS.split (sQ fr) : G) = 1 := key_s.2.1.symm
  -- conjugation
  have hconj := Work.PSU3.StageB.canon_conj_fun hS.split (sQ_coe_ne_one fr)
    (⟨d, fr.KW_le d.2⟩ : ↥(twoPoint H t))
  obtain ⟨xa, hxa, hf, hg, hh⟩ := hconj
  have hxaeq : xa = zcQ fr v hv := by
    apply Subtype.ext
    rw [hxa, hzc]
    simp only [Subgroup.coe_mk, sQ_coe]
  rw [hxaeq] at hf hg hh
  refine ⟨?_, ?_, ?_⟩
  · rw [hf, hf_s]
    rw [show (t * (↑⟨d, fr.KW_le d.2⟩ : ↥(twoPoint H t)) * t) = t * (d : G) * t from rfl,
      htd]
    group
  · rw [hg, hg_s]
    rw [show (t * (↑⟨d, fr.KW_le d.2⟩ : ↥(twoPoint H t)) * t) = t * (d : G) * t from rfl,
      htd]
    group
  · rw [hh, hh_s]
    rw [show (t * (↑⟨d, fr.KW_le d.2⟩ : ↥(twoPoint H t)) * t) = t * (d : G) * t from rfl,
      htd]
    group

/-! ## The `zcQ`-form of §2(1) -/

section Main

variable (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)

/-- The `e`-image of `zcQ v`. -/
theorem e_zcQ (hS : Work.PSU3.PSU3Hyp H Q t) (hsq : ∀ a : (Work.PSU3.E n)ˣ,
      σE (a : Work.PSU3.E n) = a → (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (e : Q ≃* SZ (Work.PSU3.E n)) (μ : (Work.PSU3.E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    (v : Work.PSU3.E n) (hv : σE v = v) :
    e (zcQ fr v hv) = ⟨0, v, by rw [hv, CharTwo.add_self_eq_zero, zero_mul]⟩ := by
  have h := e_zc_eq hS fr hsq e μ hex hes heq v hv (fr.Q0_le (fr.zc_mem v hv))
  exact SZ.ext h.1 h.2

/-- `f(zc v) = g(zc v) = zc v⁻¹`. -/
theorem fgcan_zcQ
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (v : Work.PSU3.E n) (hv : σE v = v) (hv0 : v ≠ 0) :
    (fcan hS.split (zcQ fr v hv) : G) = fr.zc v⁻¹ ∧
    (gcan hS.split (zcQ fr v hv) : G) = fr.zc v⁻¹ := by
  obtain ⟨d, hdK, hzc, hκ⟩ := zcQ_eq_conj hS fr hsq v hv hv0
  have h := canon_zcQ_of_conj hS fr hv hdK hzc
  have hσd : σE ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) =
      ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) := (fr.mem_K_iff d).mp hdK
  have hsqd : ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) ^ 2 = v := by
    rw [pow_two]; exact hκ
  have hnm : (fr.nm (fr.κ d⁻¹) : Work.PSU3.E n) = v⁻¹ := by
    rw [hsq (fr.κ d⁻¹) (by rw [map_inv]; simp [Units.val_inv_eq_inv_val, hσd])]
    rw [map_inv]
    simp only [Units.val_inv_eq_inv_val, inv_pow, hsqd, inv_inv]
  have hd1 : (d : G) * fr.zc 1 * (d : G)⁻¹ = fr.zc (v⁻¹) := by
    have h2 := fr.act_zc_K d⁻¹ ((Work.ThmF.Ksub H t).inv_mem hdK) 1 (by simp)
    rw [mul_one] at h2
    rw [hnm] at h2
    simpa using h2
  exact ⟨by rw [h.1, hd1], by rw [h.2.1, hd1]⟩

/-- `h(zc v) = d²` for the `KW`-element `d` with `κ d · κ d = v`. -/
theorem hcan_zcQ
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (v : Work.PSU3.E n) (hv : σE v = v) (hv0 : v ≠ 0) :
    ∃ d : fr.KW, (d : G) ∈ Work.ThmF.Ksub H t ∧
      (hcan hS.split (zcQ fr v hv) : G) = (d : G) * (d : G) ∧
      ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) *
        ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) = v := by
  obtain ⟨d, hdK, hzc, hκ⟩ := zcQ_eq_conj hS fr hsq v hv hv0
  exact ⟨d, hdK, (canon_zcQ_of_conj hS fr hv hdK hzc).2.2, hκ⟩

end Main
/-! ## `t` conjugates `KW` to `KW`, and the exponent of §2(2) -/

section KWconj

variable (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)

theorem conj_mul_t (hS : Work.PSU3.PSU3Hyp H Q t) (x y : G) : t * (x * y) * t = (t * x * t) * (t * y * t) :=
  StageB.conj_mul_self (t_mul_self hS) x y

theorem t_conj_zeta (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n) (d : fr.KW) (j : ℕ) : t * (fr.ζ : G) ^ j * t = (fr.ζ : G) ^ j := by
  have hζ : (MulAut.conj t) (fr.ζ : G) = (fr.ζ : G) := by
    have hmem : (fr.ζ : G) ∈ centD H t := Work.ThmF.W_le_centD H t fr.ζ_mem_W
    have hct : t * (fr.ζ : G) = (fr.ζ : G) * t :=
      (Subgroup.mem_centralizer_iff.mp hmem.2) t (by simp)
    show t * (fr.ζ : G) * t⁻¹ = fr.ζ
    rw [t_inv hS, hct, mul_assoc, t_mul_self hS, mul_one]
  have := map_pow (MulAut.conj t) (fr.ζ : G) j
  rw [hζ] at this
  have h2 : t * (fr.ζ : G) ^ j * t⁻¹ = (fr.ζ : G) ^ j := by
    simpa [MulAut.conj_apply] using this
  rw [t_inv hS] at h2
  exact h2

/-- `t d t ∈ KW`, with `κ (t d t) = (σ (κ d))⁻¹`. -/
theorem tdt_KW (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n) (d : fr.KW) : ∃ d' : fr.KW, (d' : G) = t * (d : G) * t ∧
    ((fr.κ d' : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
      = (σE ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n))⁻¹ := by
  obtain ⟨k, hk, j, hdj⟩ := fr.KW_gen d
  have hkinv : t * (k : G) * t = (k : G)⁻¹ := StageB.tconj_eq_inv hS.split fr hk
  have hzpow : t * (fr.ζ : G) ^ j * t = (fr.ζ : G) ^ j := t_conj_zeta hS fr fr.ζ j
  have hdt : (d : G) = (k : G) * (fr.ζ : G) ^ j := by rw [hdj]; rfl
  refine ⟨k⁻¹ * fr.ζ ^ j, ?_, ?_⟩
  · rw [hdt, conj_mul_t hS, hkinv, hzpow]
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv]
  · have hkfix : σE ((fr.κ k : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
        = ((fr.κ k : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) := (fr.mem_K_iff k).mp hk
    have hζnorm : ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
        * σE ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) = 1 := fr.ζ_norm
    have hσζ : σE ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
        = ((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)⁻¹ :=
      eq_inv_of_mul_eq_one_right hζnorm
    have hd' : ((fr.κ (k⁻¹ * fr.ζ ^ j) : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
        = ((fr.κ k : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)⁻¹
          * (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) ^ j := by
      simp [map_mul, Units.val_mul]
    rw [hd']
    have hdn : ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
        = ((fr.κ k : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
          * (((fr.κ fr.ζ : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)) ^ j := by
      rw [hdj]; simp [map_mul, Units.val_mul]
    rw [hdn, map_mul, map_pow, hkfix, hσζ]
    simp only [mul_inv_rev, inv_pow, inv_inv]
    ring

end KWconj

/-! ## (2) of §2: the recursion along a `Q₀`-coset -/

section Recur

variable (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
variable (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)

/-- §2(2), group form: `f(x zc v) = A⁻¹ f(f(x) zc v⁻¹) A zc v⁻¹` with `κ A = v⁻¹`. -/
theorem fcan_mul_zcQ (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    {x : Q} (hx : (x : G) ∉ fr.Q0) (v : Work.PSU3.E n)
    (hv : σE v = v) (hv0 : v ≠ 0) :
    ∃ (A : fr.KW) (_ : (A : G) ∈ Work.ThmF.Ksub H t),
      ((fr.κ A : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) = v⁻¹ ∧
      (fcan hS.split (x * zcQ fr v hv) : G) =
        (A : G)⁻¹ *
          (fcan hS.split (fcan hS.split x * zcQ fr v⁻¹ (by rw [map_inv₀, hv])) : G) *
          (A : G) * (zcQ fr v⁻¹ (by rw [map_inv₀, hv]) : G) := by
  have hxone : (1 : G) ∈ fr.Q0 := (fr.mem_Q0_iff 1 Q.one_mem).mpr (by simp)
  have hxne : (x : G) ≠ 1 := fun h => hx (by simpa [h] using hxone)
  have hzc_ne : ((zcQ fr v hv : Q) : G) ≠ 1 := zcQ_coe_ne_one fr v hv hv0
  have hxy_ne : ((x * zcQ fr v hv : Q) : G) ≠ 1 := by
    intro hcon
    have hmem : ((x * zcQ fr v hv : Q) : G) ∈ fr.Q0 := by rw [hcon]; exact hxone
    refine hx ?_
    have h2 : (x : G) = ((x * zcQ fr v hv : Q) : G) * (((zcQ fr v hv : Q) : G))⁻¹ := by
      rw [Subgroup.coe_mul]; group
    rw [h2]
    exact (fr.Q0).mul_mem hmem ((fr.Q0).inv_mem (fr.zc_mem v hv))
  obtain ⟨d, hdK, hdhc, hκ⟩ := hcan_zcQ hS fr hsq v hv hv0
  obtain ⟨d', hd'eq, hd'κ⟩ := tdt_KW hS fr d
  have hσd : σE ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)
      = ((fr.κ d : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) := (fr.mem_K_iff d).mp hdK
  have hA : (t * (hcan hS.split (zcQ fr v hv) : G) * t) = ((d' ^ 2 : fr.KW) : G) := by
    rw [hdhc]
    show t * ((d : G) * (d : G)) * t = ((d' ^ 2 : fr.KW) : G)
    rw [conj_mul_t hS, ← hd'eq, Subgroup.coe_pow fr.KW d' 2, pow_two]
  have hκA : ((fr.κ (d' ^ 2) : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) = v⁻¹ := by
    rw [map_pow]
    simp only [Units.val_pow_eq_pow_val]
    rw [hd'κ, hσd, inv_pow, pow_two, hκ]
  have hd'K : (d' : G) ∈ Work.ThmF.Ksub H t := by
    rw [hd'eq, StageB.tconj_eq_inv hS.split fr hdK]
    exact (Work.ThmF.Ksub H t).inv_mem hdK
  have hAdK : ((d' ^ 2 : fr.KW) : G) ∈ Work.ThmF.Ksub H t := by
    rw [show ((d' ^ 2 : fr.KW) : G) = (d' : G) ^ 2 from Subgroup.coe_pow fr.KW d' 2]
    exact (Work.ThmF.Ksub H t).pow_mem hd'K 2
  have hgQ : gcan hS.split (zcQ fr v hv) = (zcQ fr v⁻¹ (by rw [map_inv₀, hv]) : Q) := by
    apply Subtype.ext
    show (gcan hS.split (zcQ fr v hv) : G) = fr.zc v⁻¹
    exact (fgcan_zcQ hS fr hsq v hv hv0).2
  have hfQ : fcan hS.split (zcQ fr v hv) = (zcQ fr v⁻¹ (by rw [map_inv₀, hv]) : Q) := by
    apply Subtype.ext
    show (fcan hS.split (zcQ fr v hv) : G) = fr.zc v⁻¹
    exact (fgcan_zcQ hS fr hsq v hv hv0).1
  have h6 := (Work.PSU3.StageB.canon_mul_fun hS.split hxne hzc_ne hxy_ne).1
  refine ⟨d' ^ 2, hAdK, hκA, ?_⟩
  rw [h6, hA, hgQ, hfQ]

/-! ## (2) of §2 in the model -/

theorem e_fcan_mul_zcQ (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    (e : Q ≃* SZ (Work.PSU3.E n)) (μ : (Work.PSU3.E n)ˣ)
    (hex : ∀ x : Q, (e x).x = (μ : Work.PSU3.E n) * Multiplicative.toAdd (fr.bar x))
    (hes : ∀ hs : fr.zc 1 ∈ Q, (e ⟨fr.zc 1, hs⟩).x = 0 ∧ (e ⟨fr.zc 1, hs⟩).y = 1)
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    {x : Q} (hx : (x : G) ∉ fr.Q0) (v : Work.PSU3.E n) (hv : σE v = v) (hv0 : v ≠ 0) :
    e (fcan hS.split (x * zcQ fr v hv)) =
      SZ.torusAct ((Units.mk0 v hv0)⁻¹)
        (e (fcan hS.split (fcan hS.split x * zcQ fr v⁻¹ (by rw [map_inv₀, hv])))) *
      (⟨0, v⁻¹, by rw [map_inv₀, hv, CharTwo.add_self_eq_zero, zero_mul]⟩ :
        SZ (Work.PSU3.E n)) := by
  obtain ⟨A, hAK, hκA, hEq⟩ := fcan_mul_zcQ hS fr hsq hx v hv hv0
  have hA_H : (A : G) ∈ H := Work.RankOneUniqueness.twoPoint_le_left H t (fr.KW_le A.2)
  set z : Q := fcan hS.split x * zcQ fr v⁻¹ (by rw [map_inv₀, hv]) with hzdef
  have hzmem : (A : G)⁻¹ * ((fcan hS.split z : Q) : G) * (A : G) ∈ Q := by
    have h := Work.RankOneUniqueness.conj_mem_of_mem hS.split (H.inv_mem hA_H) (fcan hS.split z).2
    simpa using h
  let zc : Q := ⟨(A : G)⁻¹ * ((fcan hS.split z : Q) : G) * (A : G), hzmem⟩
  have hzc_eq : e zc = SZ.torusAct (fr.κ A) (e (fcan hS.split z)) :=
    heq A (fcan hS.split z) zc rfl
  have hmain : fcan hS.split (x * zcQ fr v hv) =
      zc * zcQ fr v⁻¹ (by rw [map_inv₀, hv]) := by
    apply Subtype.ext
    show (fcan hS.split (x * zcQ fr v hv) : G) =
      ((zc * zcQ fr v⁻¹ (by rw [map_inv₀, hv]) : Q) : G)
    rw [hEq]
    show (A : G)⁻¹ * ((fcan hS.split ((fcan hS.split x) * zcQ fr v⁻¹ _) : Q) : G) * (A : G)
        * (zcQ fr v⁻¹ _ : G) =
      ((zc * zcQ fr v⁻¹ (by rw [map_inv₀, hv]) : Q) : G)
    rw [← hzdef]
    show (A : G)⁻¹ * ((fcan hS.split z : Q) : G) * (A : G) * (zcQ fr v⁻¹ _ : G) =
      ((zc * zcQ fr v⁻¹ (by rw [map_inv₀, hv]) : Q) : G)
    rw [Subgroup.coe_mul]
  have hunit : fr.κ A = (Units.mk0 v hv0)⁻¹ := by
    apply Units.ext
    rw [hκA]
    rfl
  rw [hmain, map_mul, hzc_eq, hunit, e_zcQ (hS := hS) (hsq := hsq) (e := e) (μ := μ)
    (hex := hex) (hes := hes) (heq := heq) (v := v⁻¹) (hv := by rw [map_inv₀, hv])]

/-! ## (3) of §2: the recursion with the `Q₀`-factor on the left -/

theorem fcan_zcQ_mul (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (hsq : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2)
    {p : Q} (hp : (p : G) ≠ 1) {w : Work.PSU3.E n}
    (hw : σE w = w) (hw0 : w ≠ 0)
    (hzp : ((zcQ fr w hw * p : Q) : G) ≠ 1) :
    (fcan hS.split (zcQ fr w hw * p) : G) =
      (t * (hcan hS.split p : G) * t)⁻¹ *
        (fcan hS.split (zcQ fr w⁻¹ (by rw [map_inv₀, hw]) * gcan hS.split p) : G) *
        (t * (hcan hS.split p : G) * t) * (fcan hS.split p : G) := by
  have hzw : ((zcQ fr w hw : Q) : G) ≠ 1 := zcQ_coe_ne_one fr w hw hw0
  have hfQ : fcan hS.split (zcQ fr w hw) = (zcQ fr w⁻¹ (by rw [map_inv₀, hw]) : Q) := by
    apply Subtype.ext
    show (fcan hS.split (zcQ fr w hw) : G) = fr.zc w⁻¹
    exact (fgcan_zcQ hS fr hsq w hw hw0).1
  have h6 := (Work.PSU3.StageB.canon_mul_fun hS.split (x := zcQ fr w hw) (y := p)
    hzw hp hzp).1
  rw [h6, hfQ]

end Recur

end Work.PSU3.StageC
